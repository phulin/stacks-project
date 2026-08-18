import Formalization.Books.Sheaves.Unit22.RingedSpaces

/-!
# Sheaves on Spaces, Chapter 25: Ringed spaces

This file formalizes `books/sheaves.tex:3030-3107`.  The canonical
ringed-space and continuous-function constructions were already established
in Chapter 22; the declarations below expose those same definitions in the
source order for Chapter 25.

The smooth-manifold example in the source is an instance of the same
`RingedSpaceHom` interface: its smooth pullback map is the `sharp` component.
The concrete real-valued continuous-function instance is provided below by
the canonical Chapter 22 construction.
-/

namespace Formalization.Books.Sheaves.Unit25

open CategoryTheory Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10

universe v

noncomputable section

/-! ## Ringed spaces and their morphisms -/

/-- A topological space equipped with a sheaf of rings. -/
abbrev RingedSpace := Formalization.Books.Sheaves.Unit22.RingedSpace

namespace RingedSpace

/-- The underlying topological space of a ringed space. -/
abbrev topologicalSpace (X : RingedSpace.{v}) : TopCat.{v} :=
  Formalization.Books.Sheaves.Unit22.RingedSpace.topologicalSpace X

/-- The structure sheaf of a ringed space. -/
abbrev sheafOfRings (X : RingedSpace.{v}) : RingSheaf.{v, v} X.carrier :=
  Formalization.Books.Sheaves.Unit22.RingedSpace.sheafOfRings X

end RingedSpace

/-- A morphism of ringed spaces: a continuous map together with its map on
structure sheaves. -/
abbrev RingedSpaceHom (X Y : RingedSpace.{v}) :=
  Formalization.Books.Sheaves.Unit22.RingedSpaceHom X Y

/-- The category-valued `f`-map used for sheaves of rings. -/
abbrev RingSheafFMap {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : RingSheaf.{v, v} Y) (F : RingSheaf.{v, v} X) : Type _ :=
  Formalization.Books.Sheaves.Unit22.AlgebraicFMap (C := RingCat.{v}) f G F

namespace RingedSpaceHom

/-- The identity morphism of a ringed space. -/
noncomputable abbrev id (X : RingedSpace.{v}) : RingedSpaceHom X X :=
  Formalization.Books.Sheaves.Unit22.RingedSpaceHom.id X

/-- Composition of ringed-space morphisms.  The arguments are ordered as
`f` followed by `g`, so this represents `(g, g♯) ∘ (f, f♯)` in the source. -/
noncomputable abbrev comp {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) : RingedSpaceHom X Z :=
  Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp f g

/-!
The following two identities are definitional for `comp`; they make the
displayed composition formula available under the Chapter 25 names.
-/

@[simp] theorem comp_continuous {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (comp f g).continuous = f.continuous ≫ g.continuous :=
  Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp_continuous f g

theorem comp_sharp {X Y Z : RingedSpace.{v}}
    (f : RingedSpaceHom X Y) (g : RingedSpaceHom Y Z) :
    (comp f g).sharp =
      Formalization.Books.Sheaves.Unit22.algebraicFMapComp
        f.continuous g.continuous f.sharp g.sharp :=
  Formalization.Books.Sheaves.Unit22.RingedSpaceHom.comp_sharp f g

end RingedSpaceHom

/-! ## Continuous functions -/

/-- The real-valued continuous-function presheaf regarded as a presheaf of
rings. -/
abbrev realContinuousFunctionRingPresheaf (X : TopCat) :
    TopCat.Presheaf RingCat X :=
  Formalization.Books.Sheaves.Unit22.realContinuousFunctionRingPresheaf X

/-- The same continuous-function presheaf with its canonical real-algebra
structure on sections. -/
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
    Formalization.Books.Sheaves.Unit22.AlgebraicSheaf (AlgCat ℝ) X :=
  { obj := realContinuousFunctionAlgebraPresheaf X
    property :=
      (Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_iff_isSheaf
        (realContinuousFunctionAlgebraPresheaf X)).mp
        (realContinuousFunctionAlgebraPresheaf_isSheaf X) }

/-- The sheaf of real-valued continuous functions regarded as a sheaf of
rings. -/
noncomputable abbrev realContinuousFunctionRingSheaf (X : TopCat) :
    RingSheaf X :=
  Formalization.Books.Sheaves.Unit22.realContinuousFunctionRingSheaf X

/-- Pullback of a real-valued continuous function along `f`.

On sections over `V`, this is the source's rule
`h ↦ h ∘ f|_{f⁻¹(V)}`; the canonical Chapter 22 definition also supplies the
restriction compatibility and ring-map structure. -/
noncomputable abbrev continuousFunctionRingedSharp {X Y : TopCat}
    (f : X ⟶ Y) :
    RingSheafFMap f
      (realContinuousFunctionRingSheaf Y)
      (realContinuousFunctionRingSheaf X) :=
  Formalization.Books.Sheaves.Unit22.continuousFunctionRingedSharp f

/-- The continuous-function pullback is also an `ℝ`-algebra-valued `f`-map.
The ring-valued map used by `continuousFunctionRingedSharp` is its reduction
to sheaves of rings. -/
theorem continuousFunctionAlgebraSharp_exists {X Y : TopCat} (f : X ⟶ Y) :
    Nonempty
      (Formalization.Books.Sheaves.Unit22.AlgebraicFMap (C := AlgCat ℝ) f
        (realContinuousFunctionAlgebraSheaf Y)
        (realContinuousFunctionAlgebraSheaf X)) := by
  let preimageMap (V : Opens Y) :
      (Opens.toTopCat X).obj ((Opens.map f).obj V) ⟶
        (Opens.toTopCat Y).obj V :=
    TopCat.ofHom
      { toFun := fun x => ⟨f.hom x.1, x.2⟩
        continuous_toFun :=
          Continuous.subtype_mk
            (f.hom.continuous.comp continuous_subtype_val) (fun x => by
              simpa using (Opens.mem_map.mp x.2)) }
  let α : realContinuousFunctionAlgebraPresheaf Y ⟶
      (TopCat.Presheaf.pushforward (AlgCat ℝ) f).obj
        (realContinuousFunctionAlgebraPresheaf X) :=
    { app := fun V =>
        AlgCat.ofHom
          { toFun := fun g => preimageMap V.unop ≫ g
            map_one' := by
              apply TopCat.ext
              intro x
              rfl
            map_zero' := by
              apply TopCat.ext
              intro x
              rfl
            map_add' := by
              intro x y
              apply TopCat.ext
              intro z
              rfl
            map_mul' := by
              intro x y
              apply TopCat.ext
              intro z
              rfl
            commutes' := by
              intro r
              apply TopCat.ext
              intro x
              rfl }
      naturality := by
        intro U V i
        apply AlgCat.hom_ext
        apply AlgHom.ext
        intro φ
        apply TopCat.ext
        intro z
        rfl }
  exact ⟨ObjectProperty.homMk α⟩

/-- The continuous-function example gives a morphism of ringed spaces. -/
noncomputable abbrev continuousFunctionRingedSpaceHom {X Y : TopCat}
    (f : X ⟶ Y) :
    RingedSpaceHom
      ⟨X, realContinuousFunctionRingSheaf X⟩
      ⟨Y, realContinuousFunctionRingSheaf Y⟩ :=
  Formalization.Books.Sheaves.Unit22.continuousFunctionRingedSpaceHom f

end

end Formalization.Books.Sheaves.Unit25
