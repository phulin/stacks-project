import Formalization.Books.Sheaves.Unit22.RingedSpaceModules
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves on Spaces, Chapter 22, Section 6: Skyscraper sheaves and stalks

The generic skyscraper presheaf and sheaf in Mathlib is used for sets,
abelian groups, and arbitrary algebraic structures.  The module case is kept
as a source-facing interface because its scalar ring varies with the open set
and is not the ordinary skyscraper construction in a fixed module category.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit21

universe v

noncomputable section

/-! ## The point and the generic skyscraper construction -/

/-- The continuous map from the one-point space selecting `x`. -/
noncomputable def skyscraperPointMap {X : TopCat.{v}} (x : X) :
    TopCat.of PUnit.{v + 1} ⟶ X :=
  TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit.{v + 1}) x)

/-- The set-valued skyscraper presheaf at `x` with value `A`. -/
noncomputable def setSkyscraperPresheaf {X : TopCat.{v}}
    (x : X) (A : Type v) : TopCat.Presheaf (Type v) X := by
  classical
  exact skyscraperPresheaf x A

/-- The set-valued skyscraper sheaf at `x` with value `A`. -/
noncomputable def setSkyscraperSheaf {X : TopCat.{v}}
    (x : X) (A : Type v) : TopCat.Sheaf (Type v) X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the set-valued skyscraper construction. -/
noncomputable def setSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    Type v ⥤ TopCat.Sheaf (Type v) X := by
  classical
  exact skyscraperSheafFunctor x

/-- The additive-group-valued skyscraper presheaf. -/
noncomputable def abelianSkyscraperPresheaf {X : TopCat.{v}}
    (x : X) (A : AddCommGrpCat.{v}) :
    TopCat.Presheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperPresheaf x A

/-! ## Algebraic structures -/

/-- The category-valued skyscraper presheaf for any category with a terminal
object. -/
noncomputable def algebraicSkyscraperPresheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Presheaf C X := by
  classical
  exact skyscraperPresheaf x A

/-- The category-valued skyscraper sheaf for any category with a terminal
object. -/
noncomputable def algebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Sheaf C X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the category-valued skyscraper construction. -/
noncomputable def algebraicSkyscraperSheafFunctor
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) : C ⥤ TopCat.Sheaf C X := by
  classical
  exact skyscraperSheafFunctor x

/-- The additive-group-valued skyscraper sheaf. -/
noncomputable def abelianSkyscraperSheaf {X : TopCat.{v}}
    (x : X) (A : AddCommGrpCat.{v}) :
    TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the abelian-group-valued skyscraper construction. -/
noncomputable def abelianSkyscraperSheafFunctor {X : TopCat.{v}} (x : X) :
    AddCommGrpCat.{v} ⥤ TopCat.Sheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperSheafFunctor x

/-! ## The source's skyscraper predicates -/

/-- A set-valued sheaf is a skyscraper sheaf when it is isomorphic to one at
some point. -/
def IsSetSkyscraperSheaf {X : TopCat.{v}}
    (F : TopCat.Sheaf (Type v) X) : Prop :=
  ∃ x : X, ∃ A : Type v, Nonempty (F ≅ setSkyscraperSheaf x A)

/-- An abelian sheaf is a skyscraper sheaf when it is isomorphic to one at
some point. -/
def IsAbelianSkyscraperSheaf {X : TopCat.{v}}
    (F : Ab X) : Prop :=
  ∃ x : X, ∃ A : AddCommGrpCat.{v}, Nonempty (F ≅ abelianSkyscraperSheaf x A)

/-- A category-valued sheaf is a skyscraper sheaf when it is isomorphic to a
generic skyscraper sheaf. -/
def IsAlgebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (F : TopCat.Sheaf C X) : Prop :=
  ∃ x : X, ∃ A : C, Nonempty (F ≅ algebraicSkyscraperSheaf x A)

/-! ## The module-valued construction -/

/-- A source-facing module skyscraper sheaf.  Its value is a module over the
support stalk, and the induced scalar actions on sections are part of the
construction. -/
noncomputable def moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Mod O := by
  sorry

/-- The stalk functor on sheaves of `O`-modules, with its canonical stalk
module structure. -/
noncomputable def moduleStalkAddMap {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
    ((PresheafOfModules.toPresheaf O.obj).map φ.val)

theorem moduleStalkAddMap_smul {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X)
    (r : TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) :
    moduleStalkAddMap φ x ≫
        (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
          (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x))).smul r =
      (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
        (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))).smul r ≫
        moduleStalkAddMap φ x := by
  sorry

noncomputable def moduleStalkFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Mod O ⥤ ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) where
  obj F :=
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))
  map φ := ModuleCat.homMk (moduleStalkAddMap φ x) (moduleStalkAddMap_smul φ x)
  map_id := by
    sorry
  map_comp := by
    sorry

/-- Functoriality of the module skyscraper construction in its stalk-module
value. -/
noncomputable def moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O where
  obj A := moduleSkyscraperSheaf O x A
  map φ := by
    sorry
  map_id := by
    intros
    sorry
  map_comp := by
    intros
    sorry

/-- A sheaf of modules is a skyscraper sheaf when it is isomorphic to a
module skyscraper at some point. -/
def IsModuleSkyscraperSheaf {X : TopCat.{v}} (O : RingSheaf X)
    (F : Mod O) : Prop :=
  ∃ x : X,
    ∃ A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      Nonempty (F ≅ moduleSkyscraperSheaf O x A)

/-! ## Stalk calculations -/

/-- Specialization is the closure condition in the source's stalk formula. -/
theorem skyscraper_specializes_iff_mem_closure {X : TopCat.{v}}
    (x x' : X) : x ⤳ x' ↔ x' ∈ closure ({x} : Set X) :=
  specializes_iff_mem_closure

/-- The stalk of a generic skyscraper at a specialization of its support is
the prescribed value. -/
noncomputable def algebraicSkyscraperStalkOfSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}}
    (x : X) (A : C) {x' : X} (h : x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

/- The stalk of a generic skyscraper away from the closure of its support is
terminal. -/
noncomputable def algebraicSkyscraperStalkOfNotSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}}
    (x : X) (A : C) {x' : X} (h : ¬x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ terminal C := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

/-- The set-valued form of the stalk calculation at a specialization. -/
noncomputable def setSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ A := by
  exact algebraicSkyscraperStalkOfSpecializes x A h

/-- The set-valued form of the stalk calculation away from the closure. -/
noncomputable def setSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : ¬x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ terminal (Type v) := by
  exact algebraicSkyscraperStalkOfNotSpecializes x A h

/-- The abelian-group form of the stalk calculation at a specialization. -/
noncomputable def abelianSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ A := by
  exact algebraicSkyscraperStalkOfSpecializes x A h

/-- The abelian-group form of the stalk calculation away from the closure. -/
noncomputable def abelianSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : ¬x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ terminal AddCommGrpCat := by
  exact algebraicSkyscraperStalkOfNotSpecializes x A h

/-- The module stalk at the support is the prescribed stalk module. -/
theorem moduleSkyscraperStalkAtSupport
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty ((moduleStalkFunctor O x).obj
        (moduleSkyscraperSheaf O x A) ≅ A) := by
  sorry

/-! ## Stalk/skyscraper adjunctions -/

/-- The set-valued stalk/skyscraper adjunction. -/
noncomputable def setStalkSkyscraperAdjunction {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x) ⊣
      setSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

/-- The abelian-group stalk/skyscraper adjunction. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

/-- The generic algebraic-structure stalk/skyscraper adjunction. -/
noncomputable def algebraicStalkSkyscraperAdjunction
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x) ⊣
      algebraicSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

/-- The source-facing module stalk/skyscraper adjunction. -/
noncomputable def moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
