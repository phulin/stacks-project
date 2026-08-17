import Formalization.Books.Sheaves.Unit22.AbelianSheaves
import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit09.SheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 22, Section 2: Continuous maps and sheaves of
algebraic structures

Category-valued presheaves use Mathlib's canonical functors.  The source's
underlying-set compatibilities are recorded through the faithful forgetful
functor and the source's `AlgebraicStructureType` interface.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit09
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## Category-valued functors -/

/-- A category-valued presheaf on a topological space. -/
abbrev AlgebraicPresheaf (C : Type u) [Category.{v} C] (X : TopCat.{v}) :=
  TopCat.Presheaf C X

/-- A category-valued sheaf on a topological space. -/
abbrev AlgebraicSheaf (C : Type u) [Category.{v} C] (X : TopCat.{v}) :=
  TopCat.Sheaf C X

/-- The underlying set-valued presheaf of a category-valued presheaf. -/
abbrev algebraicUnderlyingPresheaf {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) {X : TopCat.{v}} (P : AlgebraicPresheaf C X) :=
  Formalization.Books.Sheaves.Unit05.underlyingPresheaf F P

/-- The underlying presheaf functor induced by a functor `C ⥤ Type v`. -/
noncomputable abbrev algebraicUnderlyingPresheafFunctor
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v) (X : TopCat.{v}) :
    AlgebraicPresheaf C X ⥤ TopCat.Presheaf (Type v) X :=
  (Functor.whiskeringRight (Opens X)ᵒᵖ C (Type v)).obj F

/-- The underlying set-valued sheaf of a category-valued sheaf. -/
noncomputable abbrev algebraicUnderlyingSheaf {C : Type u} [Category.{v} C]
    (F : C ⥤ Type v) [AlgebraicStructureType C F] {X : TopCat.{v}}
    (P : AlgebraicSheaf C X) : TopCat.Sheaf (Type v) X :=
  Formalization.Books.Sheaves.Unit16.underlyingSheaf F P

/-- The underlying sheaf morphism induced by a category-valued sheaf map. -/
abbrev algebraicUnderlyingSheafMorphism
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    {P Q : AlgebraicSheaf C X} (φ : P ⟶ Q) :
    algebraicUnderlyingSheaf F P ⟶ algebraicUnderlyingSheaf F Q :=
  Formalization.Books.Sheaves.Unit16.underlyingSheafMorphism F φ

/-- Pushforward of category-valued presheaves. -/
abbrev algebraicPresheafPushforward (C : Type u) [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicPresheaf C X ⥤ AlgebraicPresheaf C Y :=
  TopCat.Presheaf.pushforward C f

/-- Pullback of category-valued presheaves. -/
abbrev algebraicPresheafPullback (C : Type u) [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicPresheaf C Y ⥤ AlgebraicPresheaf C X :=
  TopCat.Presheaf.pullback C f

/-- Pushforward of category-valued sheaves. -/
abbrev algebraicSheafPushforward (C : Type u) [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicSheaf C X ⥤ AlgebraicSheaf C Y :=
  TopCat.Sheaf.pushforward C f

@[simp]
theorem algebraicSheafPushforward_obj_presheaf {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : AlgebraicSheaf C X) :
    ((algebraicSheafPushforward C f).obj F).presheaf =
      (algebraicPresheafPushforward C f).obj F.presheaf := rfl

/-- Pushforward of algebraic sheaves commutes with composition. -/
noncomputable def algebraicSheafPushforwardCompIso
    (C : Type u) [Category.{v} C] {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicSheafPushforward C f ⋙ algebraicSheafPushforward C g ≅
      algebraicSheafPushforward C (f ≫ g) :=
  Iso.refl _

/-- Pullback of category-valued sheaves under the standard concrete-category
assumptions used by Mathlib's sheaf pullback. -/
abbrev algebraicSheafPullback (C : Type u) [Category.{v} C]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AlgebraicSheaf C Y ⥤ AlgebraicSheaf C X :=
  TopCat.Sheaf.pullback C f

@[simp]
theorem algebraicPresheafPushforward_obj_obj {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : AlgebraicPresheaf C X) (V : Opens Y) :
    ((algebraicPresheafPushforward C f).obj F).obj (op V) =
      F.obj (op ((Opens.map f).obj V)) := rfl

@[simp]
theorem algebraicPresheafPushforward_map {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (F : AlgebraicPresheaf C X)
    {V W : Opens Y} (h : V ≤ W) :
    ((algebraicPresheafPushforward C f).obj F).map (homOfLE h).op =
      F.map (((Opens.map f).op).map (homOfLE h).op) := rfl

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

/-- The category-valued pullback is computed by the filtered neighbourhood
colimit appearing in the source. -/
noncomputable def algebraicPresheafPullback_obj_colimitIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) (U : Opens X) :
    ((algebraicPresheafPullback C f).obj G).obj (op U) ≅
      colimit (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G) :=
  Functor.leftKanExtensionObjIsoColimit (Opens.map f).op G (op U)

/-- The neighbourhood index in the pullback formula is filtered. -/
theorem algebraicPresheafPullback_index_isFiltered {X Y : TopCat.{v}}
    (f : X ⟶ Y) (U : Opens X) :
    IsFiltered (CostructuredArrow (Opens.map f).op (op U)) := by
  infer_instance

/-- The sheaf pullback is sheafification of the presheaf pullback. -/
noncomputable def algebraicSheafPullback_sheafificationIso
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasColimits C]
    [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) :
    (algebraicSheafPullback C f).obj G ≅
      (CategoryTheory.presheafToSheaf
        (Opens.grothendieckTopology X) C).obj
        ((algebraicPresheafPullback C f).obj G.presheaf) :=
  (TopCat.Sheaf.pullbackIso C f).app G

/-! ## Adjunctions and underlying-set compatibilities -/

noncomputable abbrev algebraicPresheafPullbackPushforwardAdjunction
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    algebraicPresheafPullback C f ⊣ algebraicPresheafPushforward C f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction C f

noncomputable abbrev algebraicPresheafHomEquiv
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicPresheaf C Y) (F : AlgebraicPresheaf C X) :
    ((algebraicPresheafPullback C f).obj G ⟶ F) ≃
      (G ⟶ (algebraicPresheafPushforward C f).obj F) :=
  (algebraicPresheafPullbackPushforwardAdjunction f).homEquiv G F

/-! The unit and counit expose the two maps used in the source's adjunction
argument. -/

noncomputable abbrev algebraicPresheafUnit {C : Type u} [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicPresheaf C Y) :
    G ⟶ (algebraicPresheafPushforward C f).obj
      ((algebraicPresheafPullback C f).obj G) :=
  (algebraicPresheafPullbackPushforwardAdjunction f).unit.app G

noncomputable abbrev algebraicPresheafCounit {C : Type u} [Category.{v} C]
    [HasColimits C] {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : AlgebraicPresheaf C X) :
    (algebraicPresheafPullback C f).obj
      ((algebraicPresheafPushforward C f).obj F) ⟶ F :=
  (algebraicPresheafPullbackPushforwardAdjunction f).counit.app F

/-! Pullback presheaves commute with composition, canonically. -/
noncomputable def algebraicPresheafPullbackCompIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y Z : TopCat.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    algebraicPresheafPullback C (f ≫ g) ≅
      algebraicPresheafPullback C g ⋙ algebraicPresheafPullback C f := by
  exact Adjunction.leftAdjointUniq
    (algebraicPresheafPullbackPushforwardAdjunction (f ≫ g))
    ((algebraicPresheafPullbackPushforwardAdjunction g).comp
      (algebraicPresheafPullbackPushforwardAdjunction f))

noncomputable abbrev algebraicSheafPullbackPushforwardAdjunction
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasColimits C]
    [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    algebraicSheafPullback C f ⊣ algebraicSheafPushforward C f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction C f

noncomputable abbrev algebraicSheafHomEquiv
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC] [HasColimits C]
    [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) :
    ((algebraicSheafPullback C f).obj G ⟶ F) ≃
      (G ⟶ (algebraicSheafPushforward C f).obj F) :=
  (algebraicSheafPullbackPushforwardAdjunction f).homEquiv G F

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

/-- The stalk formula for category-valued presheaf pullback. -/
noncomputable def algebraicPresheafPullbackStalkIso
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) (x : X) :
    G.stalk (f x) ≅ ((algebraicPresheafPullback C f).obj G).stalk x :=
  TopCat.Presheaf.stalkPullbackIso C f G x

/-- The source-oriented stalk isomorphism `(f_p G)_x ≅ G_{f(x)}`. -/
noncomputable def algebraicPresheafPullbackStalkIsoReverse
    {C : Type u} [Category.{v} C] [HasColimits C]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C Y) (x : X) :
    ((algebraicPresheafPullback C f).obj G).stalk x ≅ G.stalk (f x) :=
  (algebraicPresheafPullbackStalkIso f G x).symm

/-- The stalk formula for category-valued sheaf pullback. -/
theorem algebraicSheafPullback_stalk_formula
    {C : Type u} [Category.{v} C] {FC : C → C → Type*}
    {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [HasColimits C]
    [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) (x : X) :
    Nonempty
      (G.presheaf.stalk (f x) ≅
        ((algebraicSheafPullback C f).obj G).presheaf.stalk x) := by
  sorry

/-- A chosen category-valued stalk isomorphism for sheaf pullback. -/
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
  Classical.choice (algebraicSheafPullback_stalk_formula f G x)

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

/-- Pushforward and pullback preserve the source's underlying-set formulas. -/
theorem algebraicPresheafPushforward_underlying_formula
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicPresheaf C X) :
    Nonempty
      (algebraicUnderlyingPresheaf F
          ((algebraicPresheafPushforward C f).obj G) ≅
        (TopCat.Presheaf.pushforward (Type v) f).obj
          (algebraicUnderlyingPresheaf F G)) := by
  sorry

theorem algebraicPresheafPullback_underlying_formula
    {C : Type u} [Category.{v} C] [HasColimits C]
    (F : C ⥤ Type v) [PreservesFilteredColimitsOfSize.{v, v} F]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicPresheaf C Y) :
    Nonempty
      (algebraicUnderlyingPresheaf F
          ((algebraicPresheafPullback C f).obj G) ≅
          (algebraicPresheafPullback (Type v) f).obj
          (algebraicUnderlyingPresheaf F G)) := by
  sorry

/-- The underlying-set formula for the pushforward of algebraic sheaves. -/
theorem algebraicSheafPushforward_underlying_formula
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C X) :
    Nonempty
      (algebraicUnderlyingPresheaf F
          ((algebraicSheafPushforward C f).obj G).presheaf ≅
        (TopCat.Presheaf.pushforward (Type v) f).obj
          (algebraicUnderlyingPresheaf F G.presheaf)) := by
  simpa only [algebraicSheafPushforward_obj_presheaf] using
    (algebraicPresheafPushforward_underlying_formula F f G.presheaf)

/-- The underlying-set formula for the pullback of algebraic sheaves. -/
theorem algebraicSheafPullback_underlying_formula
    {C : Type u} [Category.{v} C] (F : C ⥤ Type v)
    [AlgebraicStructureType C F]
    {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{v}} (f : X ⟶ Y) (G : AlgebraicSheaf C Y) :
    Nonempty
      (algebraicUnderlyingSheaf F ((algebraicSheafPullback C f).obj G) ≅
        (TopCat.Sheaf.pullback (Type v) f).obj (algebraicUnderlyingSheaf F G)) := by
  sorry

/-! ## Algebraic `f`-maps -/

/-- An algebraic `f`-map is a morphism to the category-valued pushforward. -/
abbrev AlgebraicFMap {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AlgebraicSheaf C Y) (F : AlgebraicSheaf C X) : Type _ :=
  G ⟶ (algebraicSheafPushforward C f).obj F

/-- The component family of an algebraic `f`-map on opens of the target. -/
abbrev algebraicFMapComponents {C : Type u} [Category.{v} C]
    {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : AlgebraicSheaf C Y} {F : AlgebraicSheaf C X}
    (φ : AlgebraicFMap f G F) :
    ∀ V : Opens Y,
      G.presheaf.obj (op V) ⟶ F.presheaf.obj (op ((Opens.map f).obj V)) :=
  fun V => φ.hom.app (op V)

/-- The category-valued `f`-map is the corresponding morphism into the
pushforward sheaf. -/
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
    AlgebraicFMap (f ≫ g) H F := by
  exact ψ ≫ (algebraicSheafPushforward C g).map φ
    ≫ (algebraicSheafPushforwardCompIso C f g).hom.app F

/-- The algebraic morphism on stalks induced by an algebraic `f`-map. -/
noncomputable def algebraicFMapStalkMap
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : AlgebraicSheaf C Y} {F : AlgebraicSheaf C X}
    (ξ : AlgebraicFMap f G F) (x : X) :
    G.presheaf.stalk (f x) ⟶ F.presheaf.stalk x := by
  exact (TopCat.Presheaf.stalkFunctor C (f x)).map ξ.hom ≫
    F.presheaf.stalkPushforward C f x

/-- Algebraic stalk maps carry composition to composition. -/
theorem algebraicFMapComp_stalkMap
    {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [HasColimits C]
    {X Y Z : TopCat.{v}} {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : AlgebraicSheaf C X} {G : AlgebraicSheaf C Y} {H : AlgebraicSheaf C Z}
    (φ : AlgebraicFMap f G F) (ψ : AlgebraicFMap g H G) (x : X) :
    algebraicFMapStalkMap (algebraicFMapComp f g φ ψ) x =
      algebraicFMapStalkMap ψ (f x) ≫ algebraicFMapStalkMap φ x := by
  sorry

/-- The source's underlying-set lifting lemma: componentwise morphisms in the
algebraic category determine a unique algebraic `f`-map. -/
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
  sorry

end

end Formalization.Books.Sheaves.Unit22
