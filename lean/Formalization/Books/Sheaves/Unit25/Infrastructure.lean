import Formalization.Books.Sheaves.Unit23.Infrastructure
import Formalization.Books.Sheaves.Unit09.SheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Mathlib.Topology.Sheaves.Functors

/-!
# Shared infrastructure for Chapter 25: Ringed spaces

Ringed spaces are the source-facing pair of a topological space and a sheaf of
rings.  Their morphisms retain the continuous map and the contravariant
`f`-map on structure sheaves as separate fields.
-/

namespace Formalization.Books.Sheaves.Unit22

-- The historical namespace is retained for API compatibility.

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
      have hComm :
          TopCat.Presheaf.IsSheaf (realContinuousFunctionPresheaf X) :=
        (categoryValuedSheaf_iff_isSheaf
          (realContinuousFunctionPresheaf X)).mp
          (realContinuousFunctionPresheaf_isSheaf X)
      exact
        (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
          (CategoryTheory.forget₂ CommRingCat RingCat)
          (realContinuousFunctionPresheaf X)).mp hComm }

/-- The real-valued continuous-function presheaf with its canonical
real-algebra structure on sections. -/
abbrev realContinuousFunctionAlgebraPresheaf (X : TopCat) :
    TopCat.Presheaf (AlgCat ℝ) X :=
  Formalization.Books.Sheaves.Unit09.realContinuousFunctionAlgebraPresheaf X

/-- The real-algebra-valued continuous-function presheaf is a sheaf. -/
theorem realContinuousFunctionAlgebraPresheaf_isSheaf (X : TopCat) :
    Formalization.Books.Sheaves.Unit09.CategoryValuedSheaf
      (realContinuousFunctionAlgebraPresheaf X) :=
  Formalization.Books.Sheaves.Unit09.realContinuousFunctionAlgebraPresheaf_isSheaf X

/-- The sheaf of continuous real-valued functions with its real-algebra
structure. -/
noncomputable def realContinuousFunctionAlgebraSheaf (X : TopCat) :
    AlgebraicSheaf (AlgCat ℝ) X :=
  { obj := realContinuousFunctionAlgebraPresheaf X
    property :=
      (Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_iff_isSheaf
        (realContinuousFunctionAlgebraPresheaf X)).mp
        (realContinuousFunctionAlgebraPresheaf_isSheaf X) }

/-- Pullback of a real-valued continuous function along a continuous map is a
map of sheaves of rings. -/
noncomputable def continuousFunctionRingedSharp {X Y : TopCat}
    (f : X ⟶ Y) :
    AlgebraicFMap (C := RingCat) f
      (realContinuousFunctionRingSheaf Y)
      (realContinuousFunctionRingSheaf X) := by
  let preimageMap (V : Opens Y) :
      (Opens.toTopCat X).obj ((Opens.map f).obj V) ⟶
        (Opens.toTopCat Y).obj V :=
    TopCat.ofHom
      { toFun := fun x => ⟨f.hom x.1, x.2⟩
        continuous_toFun :=
          Continuous.subtype_mk
            (f.hom.continuous.comp continuous_subtype_val) (fun x => by
              simpa using (Opens.mem_map.mp x.2)) }
  let α : realContinuousFunctionRingPresheaf Y ⟶
      (TopCat.Presheaf.pushforward RingCat f).obj
        (realContinuousFunctionRingPresheaf X) :=
    { app := fun V =>
        (forget₂ CommRingCat RingCat).map
          (TopCat.continuousFunctions.pullback
            (preimageMap V.unop).op (TopCommRingCat.of ℝ))
      naturality := by
        intro U V i
        apply RingCat.hom_ext
        ext φ
        rfl }
  exact ObjectProperty.homMk α

/-- Continuous-function pullback is an `ℝ`-algebra-valued `f`-map. -/
theorem continuousFunctionAlgebraSharp_exists {X Y : TopCat} (f : X ⟶ Y) :
    Nonempty
      (AlgebraicFMap (C := AlgCat ℝ) f
        (realContinuousFunctionAlgebraSheaf Y)
        (realContinuousFunctionAlgebraSheaf X)) := by
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
