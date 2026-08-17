import Formalization.Books.Homology.Unit19.Filtrations
import Mathlib.Data.Int.Interval

/-!
# Exercises, Chapter 30: Filtered derived category

This file records the chapter-facing constructions.  Filtrations, graded
pieces, strict morphisms, and subobject images are the canonical interfaces
from Homology, Chapter 19.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe v u

namespace Formalization.Books.Exercises.Unit30

open Formalization.Books.Homology.Unit19

/-! ## Exercise 30.1: split filtered injectives -/

/-- The finite index set of graded pieces between two filtration bounds. -/
abbrev finiteGradedIndex (n m : ℤ) := {p : ℤ // p ∈ Finset.Icc n m}

/-- The finite biproduct of the graded pieces in a prescribed interval. -/
noncomputable def finiteGradedSum
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (n m : ℤ) : C :=
  by
    classical
    letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
    letI : Finite (finiteGradedIndex n m) := Finite.of_fintype _
    exact ⨁ fun p : finiteGradedIndex n m => gradedPiece I p.1

/-- The subobject of the finite graded sum formed by the pieces in degrees
`q ≥ p`.  This is the filtration carried by the direct-sum presentation. -/
noncomputable def finiteGradedSumStep
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (n m p : ℤ) : Subobject (finiteGradedSum I n m) := by
  classical
  letI : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  letI : Finite (finiteGradedIndex n m) := Finite.of_fintype _
  let f := biproduct.fromSubtype
    (fun q : finiteGradedIndex n m => gradedPiece I q.1)
    (fun q => p ≤ q.1)
  let hf : SplitMono f := {
    retraction := biproduct.toSubtype
      (fun q : finiteGradedIndex n m => gradedPiece I q.1)
      (fun q => p ≤ q.1)
    id := biproduct.fromSubtype_toSubtype _ _ }
  have hfmono : Mono f :=
    { right_cancellation := fun g h w => by
        calc
          g = g ≫ 𝟙 _ := (Category.comp_id g).symm
          _ = g ≫ (f ≫ hf.retraction) := by rw [hf.id]
          _ = (g ≫ f) ≫ hf.retraction := by simp [Category.assoc]
          _ = (h ≫ f) ≫ hf.retraction := by rw [w]
          _ = h ≫ (f ≫ hf.retraction) := by simp [Category.assoc]
          _ = h ≫ 𝟙 _ := by rw [hf.id]
          _ = h := Category.comp_id h }
  exact @Subobject.mk _ _ _ _ f hfmono

/-! The filtered category need not be abelian, but its biproducts are
available from the canonical filtered biproduct construction in Chapter 19.
This instance is used only to form mapping cones of filtered complexes. -/

noncomputable instance filteredHasBinaryBiproducts
    {C : Type u} [Category.{v} C] [Abelian C] :
    HasBinaryBiproducts (FilteredObject C) where
  has_binary_biproduct A B :=
    hasBinaryBiproduct_of_total
      { pt := filteredBiproduct A B
        fst := filteredBiproductDesc (𝟙 A) 0
        snd := filteredBiproductDesc 0 (𝟙 B)
        inl := filteredBiproductLift (𝟙 A) 0
        inr := filteredBiproductLift 0 (𝟙 B)
        inl_fst := by
          apply FilteredHom.ext
          change
            (biprod.lift (𝟙 A.carrier) (0 : A.carrier ⟶ B.carrier)) ≫
                biprod.desc (𝟙 A.carrier) (0 : B.carrier ⟶ A.carrier) =
              𝟙 A.carrier
          simp
        inl_snd := by
          apply FilteredHom.ext
          change
            (biprod.lift (𝟙 A.carrier) (0 : A.carrier ⟶ B.carrier)) ≫
                biprod.desc (0 : A.carrier ⟶ B.carrier) (𝟙 B.carrier) =
              (0 : A.carrier ⟶ B.carrier)
          simp
        inr_fst := by
          apply FilteredHom.ext
          change
            (biprod.lift (0 : B.carrier ⟶ A.carrier) (𝟙 B.carrier)) ≫
                biprod.desc (𝟙 A.carrier) (0 : B.carrier ⟶ A.carrier) =
              (0 : B.carrier ⟶ A.carrier)
          simp
        inr_snd := by
          apply FilteredHom.ext
          change
            (biprod.lift (0 : B.carrier ⟶ A.carrier) (𝟙 B.carrier)) ≫
                biprod.desc (0 : A.carrier ⟶ B.carrier) (𝟙 B.carrier) =
              𝟙 B.carrier
          simp }
      (by
        apply FilteredHom.ext
        change
          biprod.desc (𝟙 A.carrier) (0 : B.carrier ⟶ A.carrier) ≫
                biprod.lift (𝟙 A.carrier) (0 : A.carrier ⟶ B.carrier) +
              biprod.desc (0 : A.carrier ⟶ B.carrier) (𝟙 B.carrier) ≫
                biprod.lift (0 : B.carrier ⟶ A.carrier) (𝟙 B.carrier) =
            𝟙 (A.carrier ⊞ B.carrier)
        apply biprod.hom_ext
        · apply biprod.hom_ext' <;> simp
        · apply biprod.hom_ext' <;> simp)

/-- The filtration on `I` is transported by `e` to the direct-sum filtration
whose `p`th step is the sum of the graded pieces in degrees at least `p`. -/
def IsGradedDirectSumFiltration
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : FilteredObject C) (n m : ℤ)
    (e : I.carrier ≅ finiteGradedSum I n m) : Prop :=
  ∀ p : ℤ,
    (Subobject.«exists» e.hom).obj (I.filtration.obj p) =
      finiteGradedSumStep I n m p

end Formalization.Books.Exercises.Unit30
