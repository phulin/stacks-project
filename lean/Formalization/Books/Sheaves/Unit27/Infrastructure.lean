import Formalization.Books.Sheaves.Unit26.Infrastructure
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Shared infrastructure for Chapter 27: Skyscraper sheaves and stalks

The generic skyscraper presheaf and sheaf in Mathlib is used for sets,
abelian groups, and arbitrary algebraic structures.  The module case is kept
as a source-facing interface because its scalar ring varies with the open set
and is not the ordinary skyscraper construction in a fixed module category.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ZeroObject
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit21

universe v

noncomputable section

/-! ## The point and the generic skyscraper construction -/

/-- The continuous map from the one-point space selecting `x`. -/
noncomputable def skyscraperPointMap {X : TopCat.{v}} (x : X) :
    TopCat.of (ULift.{v} PUnit) ⟶ X :=
  TopCat.ofHom (ContinuousMap.const (TopCat.of (ULift.{v} PUnit)) x)

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

/-! The support and away-from-support stalk properties are bundled with the
module-valued construction.  This keeps the chosen object tied to its
prescribed stalk module even though the construction itself is noncomputable.
-/

structure ModuleSkyscraperData {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) where
  sheaf : Mod O
  underlying_iso :
    Nonempty (sheaf.val.presheaf ≅
      (abelianSkyscraperSheaf x (AddCommGrpCat.of (↑A))).presheaf)
  stalk_at_support :
    Nonempty (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        sheaf.val.presheaf x)) ≅ A)
  stalk_away : ∀ {x' : X}, ¬x ⤳ x' →
    Nonempty (ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x')
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v})
        sheaf.val.presheaf x')) ≅ 0)

/-- A source-facing module skyscraper sheaf.  Its value is a module over the
support stalk, and the induced scalar actions on sections are part of the
construction. -/
theorem exists_moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty (ModuleSkyscraperData O x A) := by
  sorry

/-- A source-facing module skyscraper sheaf.  Its value is a module over the
support stalk, and the induced scalar actions on sections are part of the
construction. -/
noncomputable def moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Mod O := by
  exact (Classical.choice (exists_moduleSkyscraperSheaf O x A)).sheaf

/-- Functoriality of the module skyscraper construction in its stalk-module
value. -/
structure ModuleSkyscraperFunctorData {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) where
  functor : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O
  obj_iso : ∀ A,
    Nonempty (functor.obj A ≅ moduleSkyscraperSheaf O x A)

theorem exists_moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (ModuleSkyscraperFunctorData O x) := by
  sorry

/-- Functoriality of the module skyscraper construction in its stalk-module
value. -/
noncomputable def moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O :=
  (Classical.choice (exists_moduleSkyscraperSheafFunctor O x)).functor

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

/- The stalk of a generic skyscraper is prescribed exactly on the closure of
the support and terminal away from it. -/
noncomputable def algebraicSkyscraperStalkOfMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact algebraicSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

noncomputable def algebraicSkyscraperStalkOfNotMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal C := by
  apply algebraicSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

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

noncomputable def setSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (setSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact setSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

noncomputable def setSkyscraperStalkOfNotMemClosure
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (setSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal (Type v) := by
  apply setSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

noncomputable def abelianSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (abelianSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact abelianSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

noncomputable def abelianSkyscraperStalkOfNotMemClosure
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (abelianSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal AddCommGrpCat := by
  apply abelianSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-- The module stalk at the support is the prescribed stalk module. -/
theorem moduleSkyscraperStalkAtSupport
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty ((moduleStalkFunctor O x).obj
        (moduleSkyscraperSheaf O x A) ≅ A) := by
  sorry

/- At a specialization, the module stalk is the prescribed module with
scalars restricted along the canonical specialization map. -/
theorem moduleSkyscraperStalkAtSpecialization
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x ⤳ x') :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅
      (ModuleCat.restrictScalars
        (TopCat.Presheaf.stalkSpecializes O.obj h).hom).obj A) := by
  sorry

theorem moduleSkyscraperStalkOfMemClosure
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x' ∈ closure ({x} : Set X)) :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅
      (ModuleCat.restrictScalars
        (TopCat.Presheaf.stalkSpecializes O.obj
          ((skyscraper_specializes_iff_mem_closure x x').2 h)).hom).obj A) := by
  exact moduleSkyscraperStalkAtSpecialization O x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

/-- Away from the closure of the support, a module skyscraper has the zero
stalk module. -/
theorem moduleSkyscraperStalkAwayFromSupport
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : ¬x ⤳ x') :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅ 0) := by
  sorry

theorem moduleSkyscraperStalkAwayFromClosure
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x' ∉ closure ({x} : Set X)) :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅ 0) := by
  exact moduleSkyscraperStalkAwayFromSupport O x A
    (by
      intro hs
      exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs))

/-! ## Stalk/skyscraper adjunctions -/

/-- The set-valued stalk/skyscraper adjunction. -/
noncomputable def setStalkSkyscraperAdjunction {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x) ⊣
      setSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

noncomputable abbrev setStalkSkyscraperHomEquiv {X : TopCat.{v}} (x : X)
    (F : TopCat.Sheaf (Type v) X) (A : Type v) :
    (F.presheaf.stalk x ⟶ A) ≃ (F ⟶ setSkyscraperSheaf x A) :=
  (setStalkSkyscraperAdjunction x).homEquiv F A

/-- The abelian-group stalk/skyscraper adjunction. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

noncomputable abbrev abelianStalkSkyscraperHomEquiv {X : TopCat.{v}}
    (x : X) (F : Ab X) (A : AddCommGrpCat.{v}) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ abelianSkyscraperSheaf x A) :=
  (abelianStalkSkyscraperAdjunction x).homEquiv F A

/-- The generic algebraic-structure stalk/skyscraper adjunction. -/
noncomputable def algebraicStalkSkyscraperAdjunction
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x) ⊣
      algebraicSkyscraperSheafFunctor x :=
  by
    letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
    exact stalkSkyscraperSheafAdjunction x

noncomputable abbrev algebraicStalkSkyscraperHomEquiv
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (F : TopCat.Sheaf C X) (A : C) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ algebraicSkyscraperSheaf x A) :=
  (algebraicStalkSkyscraperAdjunction x).homEquiv F A

/-- The source-facing module stalk/skyscraper adjunction. -/
theorem exists_moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x) := by
  sorry

/-- The source-facing module stalk/skyscraper adjunction. -/
noncomputable def moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x := by
  exact Classical.choice (exists_moduleStalkSkyscraperAdjunction O x)

noncomputable abbrev moduleStalkSkyscraperHomEquiv {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) (F : Mod O)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    ((moduleStalkFunctor O x).obj F ⟶ A) ≃
      (F ⟶ (moduleSkyscraperSheafFunctor O x).obj A) :=
  (moduleStalkSkyscraperAdjunction O x).homEquiv F A

end

end Formalization.Books.Sheaves.Unit22
