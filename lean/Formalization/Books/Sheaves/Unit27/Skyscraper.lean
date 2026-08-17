import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves on Spaces, Chapter 27: Skyscraper sheaves and stalks

This file formalizes `books/sheaves.tex:3269-3366`.  Mathlib's canonical
skyscraper presheaf and sheaf are used for sets, abelian groups, and general
category-valued sheaves.  The module-valued construction is expressed with a
chosen sheaf of modules whose underlying additive sheaf is the canonical
abelian skyscraper; its support and away-from-support stalk interfaces retain
the scalar structures required by the source.

Stalk equalities are represented by canonical categorical isomorphisms, and
the displayed Hom identities are represented by the corresponding adjunction
Hom equivalences.
-/

namespace Formalization.Books.Sheaves.Unit27

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit10
open scoped ZeroObject

universe v

noncomputable section

/-! ## The skyscraper construction -/

/-- The point map used to realize a skyscraper as a point pushforward. -/
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

/-- The abelian-group-valued skyscraper presheaf and sheaf. -/
noncomputable def abelianSkyscraperPresheaf {X : TopCat.{v}}
    (x : X) (A : AddCommGrpCat.{v}) :
    TopCat.Presheaf AddCommGrpCat.{v} X := by
  classical
  exact skyscraperPresheaf x A

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

/-- The generic algebraic-structure-valued skyscraper presheaf and sheaf. -/
noncomputable def algebraicSkyscraperPresheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Presheaf C X := by
  classical
  exact skyscraperPresheaf x A

noncomputable def algebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) (A : C) : TopCat.Sheaf C X := by
  classical
  exact skyscraperSheaf x A

/-- Functoriality of the algebraic-structure-valued construction. -/
noncomputable def algebraicSkyscraperSheafFunctor
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (x : X) : C ⥤ TopCat.Sheaf C X := by
  classical
  exact skyscraperSheafFunctor x

/-! ## The four skyscraper-sheaf predicates -/

/-- A set-valued sheaf is a skyscraper sheaf when it is isomorphic to one at a
point. -/
def IsSetSkyscraperSheaf {X : TopCat.{v}}
    (F : TopCat.Sheaf (Type v) X) : Prop :=
  ∃ x : X, ∃ A : Type v, Nonempty (F ≅ setSkyscraperSheaf x A)

/-- An abelian sheaf is a skyscraper sheaf when it is isomorphic to one at a
point. -/
def IsAbelianSkyscraperSheaf {X : TopCat.{v}}
    (F : Ab X) : Prop :=
  ∃ x : X, ∃ A : AddCommGrpCat.{v}, Nonempty (F ≅ abelianSkyscraperSheaf x A)

/-- A sheaf of algebraic structures is a skyscraper sheaf when it is
isomorphic to one at a point. -/
def IsAlgebraicSkyscraperSheaf
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C]
    {X : TopCat.{v}} (F : TopCat.Sheaf C X) : Prop :=
  ∃ x : X, ∃ A : C, Nonempty (F ≅ algebraicSkyscraperSheaf x A)

/-! The module-valued construction -/

/-- Data for a module-valued skyscraper sheaf with prescribed support stalk. -/
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

/-- Existence of the module-valued skyscraper construction. -/
theorem exists_moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty (ModuleSkyscraperData O x A) := by
  sorry

/-- A chosen sheaf of `O`-modules representing the skyscraper with value `A`.
-/
noncomputable def moduleSkyscraperSheaf {X : TopCat.{v}}
    (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Mod O := by
  exact (Classical.choice (exists_moduleSkyscraperSheaf O x A)).sheaf

/-- The underlying additive morphism on module stalks. -/
noncomputable def moduleStalkAddMap {X : TopCat.{v}} {O : RingSheaf X}
    {F G : Mod O} (φ : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) G.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
    ((PresheafOfModules.toPresheaf O.obj).map φ.val)

/-- The stalk map is linear over the stalk of the scalar sheaf. -/
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

/-- The stalk functor on sheaves of `O`-modules, with its canonical stalk
module structure. -/
noncomputable def moduleStalkFunctor {X : TopCat.{v}} (O : RingSheaf X)
    (x : X) :
    Mod O ⥤ ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) where
  obj F :=
    ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)
      (↑(TopCat.Presheaf.stalk (C := AddCommGrpCat.{v}) F.val.presheaf x))
  map φ := ModuleCat.homMk (moduleStalkAddMap φ x) (moduleStalkAddMap_smul φ x)
  map_id := by
    sorry
  map_comp := by
    sorry

/-- Data expressing functoriality of the module-valued skyscraper. -/
structure ModuleSkyscraperFunctorData {X : TopCat.{v}} (O : RingSheaf X)
    (x : X) where
  functor : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O
  obj_iso : ∀ A,
    Nonempty (functor.obj A ≅ moduleSkyscraperSheaf O x A)

/-- Existence of the module-valued skyscraper functor. -/
theorem exists_moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (ModuleSkyscraperFunctorData O x) := by
  sorry

/-- A chosen functor from support-stalk modules to module skyscraper sheaves. -/
noncomputable def moduleSkyscraperSheafFunctor {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x) ⥤ Mod O :=
  (Classical.choice (exists_moduleSkyscraperSheafFunctor O x)).functor

/-- A sheaf of `O`-modules is a skyscraper sheaf when it is isomorphic to one
with value a module over a support stalk. -/
def IsModuleSkyscraperSheaf {X : TopCat.{v}} (O : RingSheaf X)
    (F : Mod O) : Prop :=
  ∃ x : X,
    ∃ A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x),
      Nonempty (F ≅ moduleSkyscraperSheaf O x A)

/-! ## The stalk calculation -/

/-- Specialization is equivalent to membership in the closure of the support.
-/
theorem skyscraper_specializes_iff_mem_closure {X : TopCat.{v}}
    (x x' : X) : x ⤳ x' ↔ x' ∈ closure ({x} : Set X) :=
  specializes_iff_mem_closure

/-- The generic stalk calculation at a specialization of the support. -/
noncomputable def algebraicSkyscraperStalkOfSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X} (h : x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

/-- The generic stalk calculation away from the closure of the support. -/
noncomputable def algebraicSkyscraperStalkOfNotSpecializes
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X} (h : ¬x ⤳ x') :
    (algebraicSkyscraperPresheaf x A).stalk x' ≅ terminal C := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

/-- The generic stalk is the prescribed value at every point in the closure of
the support. -/
noncomputable def algebraicSkyscraperStalkOfMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∈ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ A := by
  exact algebraicSkyscraperStalkOfSpecializes x A
    ((skyscraper_specializes_iff_mem_closure x x').2 h)

/-- The generic stalk is terminal at every point outside the closure of the
support. -/
noncomputable def algebraicSkyscraperStalkOfNotMemClosure
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (A : C) {x' : X}
    (h : x' ∉ closure ({x} : Set X)) :
    (algebraicSkyscraperSheaf x A).presheaf.stalk x' ≅ terminal C := by
  apply algebraicSkyscraperStalkOfNotSpecializes x A
  intro hs
  exact h ((skyscraper_specializes_iff_mem_closure x x').1 hs)

/-- The set-valued stalk calculation at and away from the closure. -/
noncomputable def setSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

noncomputable def setSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : Type v) {x' : X} (h : ¬x ⤳ x') :
    (setSkyscraperPresheaf x A).stalk x' ≅ terminal (Type v) := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

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

/-- The abelian-group stalk calculation at and away from the closure. -/
noncomputable def abelianSkyscraperStalkOfSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ A := by
  classical
  exact skyscraperPresheafStalkOfSpecializes x A h

noncomputable def abelianSkyscraperStalkOfNotSpecializes
    {X : TopCat.{v}} (x : X) (A : AddCommGrpCat.{v}) {x' : X}
    (h : ¬x ⤳ x') :
    (abelianSkyscraperPresheaf x A).stalk x' ≅ terminal AddCommGrpCat := by
  classical
  exact skyscraperPresheafStalkOfNotSpecializes x A h

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

/-- At the support, a module skyscraper has its prescribed stalk module. -/
theorem moduleSkyscraperStalkAtSupport
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    Nonempty ((moduleStalkFunctor O x).obj
      (moduleSkyscraperSheaf O x A) ≅ A) := by
  sorry

/-- At a specialization of the support, the module stalk is the prescribed
module with scalars restricted along the canonical stalk specialization map.
-/
theorem moduleSkyscraperStalkAtSpecialization
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x ⤳ x') :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅
      (ModuleCat.restrictScalars
        (TopCat.Presheaf.stalkSpecializes O.obj h).hom).obj A) := by
  sorry

/-- Closure-form version of the module stalk calculation at the support. -/
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

/-- Away from the closure of the support, a module skyscraper has zero stalk.
-/
theorem moduleSkyscraperStalkAwayFromClosure
    {X : TopCat.{v}} (O : RingSheaf X) (x : X)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x))
    {x' : X} (h : x' ∉ closure ({x} : Set X)) :
    Nonempty ((moduleStalkFunctor O x').obj
      (moduleSkyscraperSheaf O x A) ≅ 0) := by
  sorry

/-! ## The stalk/skyscraper adjunctions -/

/-- The set-valued stalk/skyscraper adjunction. -/
noncomputable def setStalkSkyscraperAdjunction {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget (Type v) X ⋙
      TopCat.Presheaf.stalkFunctor (Type v) x) ⊣
      setSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the set-valued adjunction. -/
noncomputable abbrev setStalkSkyscraperHomEquiv {X : TopCat.{v}} (x : X)
    (F : TopCat.Sheaf (Type v) X) (A : Type v) :
    (F.presheaf.stalk x ⟶ A) ≃ (F ⟶ setSkyscraperSheaf x A) :=
  (setStalkSkyscraperAdjunction x).homEquiv F A

/-- The abelian-group stalk/skyscraper adjunction. -/
noncomputable def abelianStalkSkyscraperAdjunction {X : TopCat.{v}}
    (x : X) :
    (TopCat.Sheaf.forget AddCommGrpCat.{v} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{v} x) ⊣
      abelianSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the abelian-group adjunction. -/
noncomputable abbrev abelianStalkSkyscraperHomEquiv {X : TopCat.{v}} (x : X)
    (F : Ab X) (A : AddCommGrpCat.{v}) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ abelianSkyscraperSheaf x A) :=
  (abelianStalkSkyscraperAdjunction x).homEquiv F A

/-- The generic algebraic-structure stalk/skyscraper adjunction. -/
noncomputable def algebraicStalkSkyscraperAdjunction
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) :
    (TopCat.Sheaf.forget C X ⋙ TopCat.Presheaf.stalkFunctor C x) ⊣
      algebraicSkyscraperSheafFunctor x := by
  letI : ∀ U : Opens X, Decidable (x ∈ U) := fun _ => Classical.dec _
  exact stalkSkyscraperSheafAdjunction x

/-- The Hom equivalence for the algebraic-structure adjunction. -/
noncomputable abbrev algebraicStalkSkyscraperHomEquiv
    {C : Type (v + 1)} [Category.{v} C] [HasTerminal C] [HasColimits C]
    {X : TopCat.{v}} (x : X) (F : TopCat.Sheaf C X) (A : C) :
    (F.presheaf.stalk x ⟶ A) ≃
      (F ⟶ algebraicSkyscraperSheaf x A) :=
  (algebraicStalkSkyscraperAdjunction x).homEquiv F A

/-- Existence of the module stalk/skyscraper adjunction. -/
theorem exists_moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    Nonempty (moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x) := by
  sorry

/-- The module stalk/skyscraper adjunction. -/
noncomputable def moduleStalkSkyscraperAdjunction {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) :
    moduleStalkFunctor O x ⊣ moduleSkyscraperSheafFunctor O x := by
  exact Classical.choice (exists_moduleStalkSkyscraperAdjunction O x)

/-- The Hom equivalence for the module stalk/skyscraper adjunction. -/
noncomputable abbrev moduleStalkSkyscraperHomEquiv {X : TopCat.{v}}
    (O : RingSheaf X) (x : X) (F : Mod O)
    (A : ModuleCat.{v} (TopCat.Presheaf.stalk (C := RingCat.{v}) O.obj x)) :
    ((moduleStalkFunctor O x).obj F ⟶ A) ≃
      (F ⟶ (moduleSkyscraperSheafFunctor O x).obj A) :=
  (moduleStalkSkyscraperAdjunction O x).homEquiv F A

end

end Formalization.Books.Sheaves.Unit27
