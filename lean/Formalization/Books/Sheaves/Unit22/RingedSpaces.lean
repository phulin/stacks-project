import Formalization.Books.Sheaves.Unit22.AlgebraicStructures
import Formalization.Books.Sheaves.Unit09.SheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Mathlib.Topology.Sheaves.Functors

/-!
# Sheaves on Spaces, Chapter 22, Section 4: Ringed spaces

Ringed spaces are the source-facing pair of a topological space and a sheaf of
rings.  Their morphisms retain the continuous map and the contravariant
`f`-map on structure sheaves as separate fields.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit09
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

/-! ## Ringed spaces and their morphisms -/

/-- A topological space equipped with a sheaf of rings. -/
structure RingedSpace where
  carrier : TopCat.{v}
  structureSheaf : RingSheaf.{v, v} carrier

namespace RingedSpace

instance : CoeSort (RingedSpace.{v}) (Type v) :=
  ⟨fun X => X.carrier⟩

instance : Coe (RingedSpace.{v}) (TopCat.{v}) :=
  ⟨RingedSpace.carrier⟩

/-- The underlying topological space of a ringed space. -/
abbrev topologicalSpace (X : RingedSpace.{v}) : TopCat.{v} := X.carrier

/-- The structure sheaf of a ringed space. -/
abbrev sheafOfRings (X : RingedSpace.{v}) : RingSheaf.{v, v} X.carrier :=
  X.structureSheaf

end RingedSpace

/-- A morphism of ringed spaces: a continuous map together with its map on
structure sheaves. -/
structure RingedSpaceHom (X Y : RingedSpace.{v}) where
  continuous : X.carrier ⟶ Y.carrier
  sharp : AlgebraicFMap (C := RingCat.{v}) continuous
    Y.structureSheaf X.structureSheaf

namespace RingedSpaceHom

/-- The identity morphism of a ringed space. -/
noncomputable def id (X : RingedSpace.{v}) : RingedSpaceHom X X where
  continuous := 𝟙 X.carrier
  sharp := by
    exact 𝟙 X.structureSheaf

/-- Composition of morphisms of ringed spaces. -/
noncomputable def comp {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) : RingedSpaceHom X Z where
  continuous := f.continuous ≫ g.continuous
  sharp := algebraicFMapComp f.continuous g.continuous f.sharp g.sharp

/-- The continuous component of the composite is the composite continuous
map. -/
@[simp] theorem comp_continuous {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (comp f g).continuous = f.continuous ≫ g.continuous := rfl

/-- The structure-sheaf component of a composite is the composite of the
corresponding `f`-maps. -/
theorem comp_sharp {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (comp f g).sharp = algebraicFMapComp f.continuous g.continuous f.sharp g.sharp := rfl

end RingedSpaceHom

/-- The category of ringed spaces and ringed-space morphisms. -/
instance : Category (RingedSpace.{v}) where
  Hom := RingedSpaceHom
  id := RingedSpaceHom.id
  comp f g := RingedSpaceHom.comp f g
  id_comp f := by
    cases f
    rfl
  comp_id f := by
    cases f
    rfl
  assoc f g h := by
    cases f
    cases g
    cases h
    rfl

/-! ## Continuous functions -/

/-- The real-valued continuous-function presheaf regarded as a presheaf of
rings. -/
abbrev realContinuousFunctionRingPresheaf (X : TopCat) :
    TopCat.Presheaf RingCat X :=
  (Formalization.Books.Sheaves.Unit09.realContinuousFunctionPresheaf X) ⋙
    (forget₂ CommRingCat RingCat)

/-- The sheaf of real-valued continuous functions regarded as a sheaf of
rings. -/
noncomputable def realContinuousFunctionRingSheaf (X : TopCat) :
    RingSheaf X :=
  { obj := realContinuousFunctionRingPresheaf X
    property := by
      sorry }

/-- Pullback of a real-valued continuous function along a continuous map is a
map of sheaves of rings. -/
noncomputable def continuousFunctionRingedSharp {X Y : TopCat}
    (f : X ⟶ Y) :
    AlgebraicFMap (C := RingCat) f
      (realContinuousFunctionRingSheaf Y)
      (realContinuousFunctionRingSheaf X) := by
  sorry

/-- The continuous-function construction gives a ringed-space morphism. -/
noncomputable def continuousFunctionRingedSpaceHom {X Y : TopCat}
    (f : X ⟶ Y) :
    RingedSpaceHom
      ⟨X, realContinuousFunctionRingSheaf X⟩
      ⟨Y, realContinuousFunctionRingSheaf Y⟩ :=
  { continuous := f
    sharp := continuousFunctionRingedSharp f }

end

end Formalization.Books.Sheaves.Unit22
