import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-!
# Sheaves on Spaces, Chapter 6: Presheaves of modules

The source section is formalized with Mathlib's canonical
`PresheafOfModules` construction.  Its objects carry a module over the ring
assigned to every open and semilinear restriction maps; its morphisms are the
componentwise linear maps satisfying the naturality condition.  Thus the
canonical structure subsumes the source's equivalent presentation by an
abelian presheaf with an action of the presheaf of rings.

For a morphism of presheaves of rings, Mathlib's presheaf change-of-rings
API supplies restriction of scalars and the canonical left-adjoint
`pullback`.  The latter provides the categorical change-of-rings interface
for the pointwise tensor-product construction in the source.
-/

namespace Formalization.Books.Sheaves.Unit06

open CategoryTheory Opposite TopologicalSpace
open scoped ChangeOfRings

universe w v

/-! ## Presheaves of rings and modules -/

/-- A presheaf of rings on `X`, represented by Mathlib's canonical functor. -/
abbrev RingPresheaf (X : TopCat.{v}) := TopCat.Presheaf (RingCat.{w}) X

/-- A morphism of presheaves of rings. -/
abbrev RingPresheafMorphism {X : TopCat.{v}} {O₁ O₂ : RingPresheaf.{w, v} X} :=
  O₁ ⟶ O₂

/-- A presheaf of modules over a presheaf of rings. -/
abbrev PresheafOfOModules {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  _root_.PresheafOfModules.{w} O

/-- The category `PMod(O)` of presheaves of `O`-modules. -/
abbrev PMod {X : TopCat.{v}} (O : RingPresheaf.{w, v} X) :=
  PresheafOfOModules O

/-- A morphism of presheaves of `O`-modules. -/
abbrev PresheafOfOModulesMorphism {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O} := F ⟶ G

/-- The source's `Hom_O(F, G)`, represented by the canonical hom type. -/
abbrev OModuleHom {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F G : PMod O) := F ⟶ G

/-- The abelian-group-valued presheaf underlying a presheaf of modules. -/
noncomputable abbrev underlyingAbelianPresheaf {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} (F : PMod O) := F.presheaf

/-- The module of sections over an open set. -/
abbrev moduleOn {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) (U : Opens X) := F.obj (op U)

/-- The restriction morphism of a presheaf of modules along an open inclusion. -/
abbrev moduleRestriction {X : TopCat.{v}} {O : RingPresheaf.{w, v} X}
    (F : PMod O) {U V : Opens X} (h : V ≤ U) :
    F.obj (op U) ⟶
      (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).obj (F.obj (op V)) :=
  F.map (homOfLE h).op

/-!
The following theorem exposes the source's commuting restriction square in
the canonical `PresheafOfModules.Hom` interface.  The module action and the
linearity of every component are fields of the canonical bundled modules.
-/

/-- A morphism of presheaves of modules commutes with restriction maps. -/
theorem presheafOfOModulesMorphism_naturality {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G))
    {U V : Opens X} (h : V ≤ U) :
    moduleRestriction F h ≫
        (ModuleCat.restrictScalars (O.map (homOfLE h).op).hom).map
          (φ.app (op V)) =
      φ.app (op U) ≫ moduleRestriction G h := by
  exact φ.naturality (homOfLE h).op

/-- Every component of an `O`-module morphism is linear over the sections. -/
theorem presheafOfOModulesMorphism_smul {X : TopCat.{v}}
    {O : RingPresheaf.{w, v} X} {F G : PMod O}
    (φ : PresheafOfOModulesMorphism (F := F) (G := G)) (U : Opens X)
    (r : O.obj (op U)) (m : F.obj (op U)) :
    φ.app (op U) (r • m) = r • φ.app (op U) m := by
  exact (φ.app (op U)).hom.map_smul r m

/-!
`PresheafOfModules.pullback` is parameterized by a functor between the
indexing categories.  For the present section that functor is the identity
on `Opens X`; this helper only changes the type of the ring morphism and
introduces no additional mathematical data.
-/

/-- View a ring-presheaf morphism as one over the identity on the opens. -/
noncomputable def asIdentityRingPresheafMorphism {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    O₁ ⟶ (𝟭 (Opens X)).op ⋙ O₂ := by
  exact α ≫
    (Functor.isoWhiskerRight (Functor.opId (Opens X)) O₂ ≪≫
      Functor.leftUnitor O₂).inv

/-! ## Restriction of scalars -/

/-- Restriction of scalars for a morphism of presheaves of rings. -/
noncomputable abbrev restrictionOfScalars {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) :
    PMod O₂ ⥤ PMod O₁ :=
  _root_.PresheafOfModules.pushforward
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The restriction of an individual presheaf of modules to the smaller ring. -/
noncomputable abbrev restrictedModule {X : TopCat.{v}}
    {O₁ O₂ : RingPresheaf.{w, v} X} (α : O₁ ⟶ O₂) (F : PMod O₂) : PMod O₁ :=
  (restrictionOfScalars α).obj F

/-! ## Tensor product and change of rings -/

/-!
The Mathlib pullback existence theorem is stated for a small indexing
category and a presheaf of rings in the same universe.  The change-of-rings
interface below follows that established universe convention for `Opens X`;
the imported canonical instance supplies the right adjoint for the
restriction-of-scalars functor.
-/

/-!
This private spelling keeps the source order: the tensor-product object is
introduced before the public change-of-rings functor, while both reuse the
same canonical pullback functor.
-/

noncomputable abbrev changeOfRingsCore {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  _root_.PresheafOfModules.pullback
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The tensor product presheaf described in the source. -/
noncomputable abbrev tensorProductPresheaf {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) (G : PMod O₁) : PMod O₂ :=
  (changeOfRingsCore α).obj G

/-- A presheaf of commutative rings, viewed before forgetting to `RingCat`. -/
abbrev CommRingPresheaf (X : TopCat.{w}) :=
  TopCat.Presheaf (CommRingCat.{w}) X

/-- A presheaf of modules over a commutative-ring presheaf. -/
abbrev CommRingPresheafModule {X : TopCat.{w}} (O : CommRingPresheaf X) :=
  PMod (O ⋙ (forget₂ CommRingCat RingCat))

/-- The underlying `RingCat` morphism of a commutative-ring-presheaf map. -/
abbrev commRingPresheafMorphismToRingPresheaf
    {X : TopCat.{w}} {O₁ O₂ : CommRingPresheaf X} (α : O₁ ⟶ O₂) :
    (O₁ ⋙ (forget₂ CommRingCat RingCat)) ⟶
      (O₂ ⋙ (forget₂ CommRingCat RingCat)) :=
  Functor.whiskerRight α (forget₂ CommRingCat RingCat)

/-- The change-of-rings functor `PMod(O₁) ⥤ PMod(O₂)`. -/
noncomputable abbrev changeOfRings {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    PMod O₁ ⥤ PMod O₂ :=
  changeOfRingsCore α

/-! ## Adjointness -/

/-- Change of rings is left adjoint to restriction of scalars. -/
noncomputable def changeOfRingsAdjunction {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂) :
    changeOfRings α ⊣ restrictionOfScalars α :=
  _root_.PresheafOfModules.pullbackPushforwardAdjunction
    (F := 𝟭 (Opens X)) (asIdentityRingPresheafMorphism α)

/-- The source-facing Hom bijection for change of rings and restriction. -/
noncomputable def changeOfRingsHomEquiv {X : TopCat.{w}}
    {O₁ O₂ : RingPresheaf.{w, w} X} (α : O₁ ⟶ O₂)
    (G : PMod O₁) (F : PMod O₂) :
    (G ⟶ restrictedModule α F) ≃
      (tensorProductPresheaf α G ⟶ F) := by
  exact (changeOfRingsAdjunction α).homEquiv G F |>.symm

end Formalization.Books.Sheaves.Unit06
