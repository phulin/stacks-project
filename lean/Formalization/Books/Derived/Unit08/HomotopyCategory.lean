import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories

/-!
# Derived Categories, Chapter 8: the homotopy category

The source uses `Comp(𝒜)` for cochain complexes in an additive category and
`K(𝒜)` for their homotopy category.  Mathlib already supplies the canonical
cochain-complex, homotopy, quotient, and bounded-below APIs.  The bounded-above
and bounded object properties below use the same canonical support predicates
and the quotient's strict image construction.
-/

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit03

universe v u

namespace Formalization.Books.Derived.Unit08

/- The source's additive-category interface supplies finite biproducts; this
   standard Mathlib bridge supplies the binary instance required by the
   homotopy-category triangulation API. -/
noncomputable instance additiveCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Complexes and their boundedness -/

/-- The source's `Comp(𝒜) = CoCh(𝒜)`, represented by integer-indexed cochain complexes. -/
abbrev Comp (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex C ℤ

/-- A cochain complex is bounded below when it is eventually zero in negative degrees. -/
abbrev IsBoundedBelow
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  CochainComplex.plus C K

/-- A cochain complex is bounded above when it is eventually zero in positive degrees. -/
def IsBoundedAbove
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  ∃ n : ℤ, K.IsStrictlyLE n

/-- A cochain complex is bounded when it is eventually zero in both directions. -/
def IsBounded
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  ∃ p q : ℤ, K.IsStrictlyGE p ∧ K.IsStrictlyLE q

/-- The object property of bounded-below cochain complexes. -/
abbrev boundedBelowProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  CochainComplex.plus C

/-- The object property of bounded-above cochain complexes. -/
def boundedAboveProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  fun K => IsBoundedAbove K

/-- The object property of bounded cochain complexes. -/
def boundedProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  fun K => IsBounded K

/-- The source's `Comp⁺(𝒜)`, using Mathlib's canonical full subcategory. -/
abbrev CompPlus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex.Plus C

/-- The source's `Comp⁻(𝒜)`, the full subcategory of bounded-above complexes. -/
abbrev CompMinus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedAboveProperty C).FullSubcategory

/-- The source's `Compᵇ(𝒜)`, the full subcategory of bounded complexes. -/
abbrev CompBounded (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedProperty C).FullSubcategory

/-! ## Homotopy categories -/

/-- The source's `K(𝒜)`, represented by Mathlib's homotopy category of cochain complexes. -/
abbrev K (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory C (.up ℤ)

/-- The bounded-below property on `K(𝒜)`, from Mathlib's homotopy-category API. -/
abbrev boundedBelowHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  HomotopyCategory.plus C

/-- The bounded-above property on `K(𝒜)`, transported along the quotient. -/
def boundedAboveHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  (boundedAboveProperty C).strictMap (HomotopyCategory.quotient C (.up ℤ))

/-- The bounded property on `K(𝒜)`, transported along the quotient. -/
def boundedHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  (boundedProperty C).strictMap (HomotopyCategory.quotient C (.up ℤ))

/-- The source's `K⁺(𝒜)`, using Mathlib's canonical bounded-below homotopy category. -/
abbrev KPlus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory.Plus C

/-- The source's `K⁻(𝒜)`, the full subcategory of bounded-above homotopy objects. -/
abbrev KMinus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedAboveHomotopyProperty C).FullSubcategory

/-- The source's `Kᵇ(𝒜)`, the full subcategory of bounded homotopy objects. -/
abbrev KBounded (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedHomotopyProperty C).FullSubcategory

/-!
The source next records that these four categories are triangulated.  The
ambient and bounded-below cases are already instances in Mathlib.  The
bounded-above and bounded cases are the two source-facing interfaces not
provided by the current Mathlib API; their proofs belong to the subsequent
cone and distinguished-triangle development.
-/

noncomputable instance boundedAboveHomotopyProperty_isTriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedAboveHomotopyProperty C).IsTriangulated := by
  sorry

noncomputable instance boundedHomotopyProperty_isTriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedHomotopyProperty C).IsTriangulated := by
  sorry

end Formalization.Books.Derived.Unit08
