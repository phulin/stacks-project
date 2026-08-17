import Formalization.Books.Simplicial.Unit13.ProductsWithSimplicialSets
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Yoneda

/-!
# Simplicial Methods, Chapter 16: Internal Hom

The source uses products of simplicial objects and the previously constructed
coproduct-based product of a simplicial set with a simplicial object.  The
former is Mathlib's categorical product in the functor category; the latter is
`Unit13.simplicialSetProduct`.  Representability is expressed by Mathlib's
`Functor.RepresentableBy` interface.
-/

namespace Formalization.Books.Simplicial.Unit16

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

/-! ## The finite nonempty product hypotheses -/

/-- A category has the source's finite nonempty products. -/
abbrev HasFiniteNonemptyProducts (C : Type u) [Category.{v} C] : Prop :=
  ∀ n : ℕ, HasLimitsOfShape (Discrete (Fin (n + 1))) C

/-- A category has finite nonempty coproducts, needed by `Δ[n] × V`. -/
abbrev HasFiniteNonemptyCoproducts (C : Type u) [Category.{v} C] : Prop :=
  ∀ n : ℕ, HasColimitsOfShape (Discrete (Fin (n + 1))) C

/-- The binary products needed for products of simplicial objects. -/
theorem hasBinaryProducts_of_hasFiniteNonemptyProducts
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C) : HasBinaryProducts C := by
  sorry

/-- The binary coproducts needed for the earlier `Δ[n] × V` construction. -/
theorem hasBinaryCoproducts_of_hasFiniteNonemptyCoproducts
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyCoproducts C) : HasBinaryCoproducts C := by
  sorry

/-! ## Products of simplicial objects and the representing functor -/

/-- The categorical product of two simplicial objects under the source hypothesis. -/
noncomputable abbrev simplicialProduct
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (W V : SimplicialObject C) : SimplicialObject C :=
  letI : HasBinaryProducts C :=
    hasBinaryProducts_of_hasFiniteNonemptyProducts hC
  Limits.prod W V

/-- The source's contravariant functor `W ↦ Hom(W × V, U)`. -/
noncomputable def internalHomFunctor
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C) :
    (SimplicialObject C)ᵒᵖ ⥤ Type v := by
  letI : HasBinaryProducts C :=
    hasBinaryProducts_of_hasFiniteNonemptyProducts hC
  exact
    { obj := fun W => (Limits.prod W.unop V ⟶ U)
      map := fun {W W'} f =>
        TypeCat.ofHom (fun g : Limits.prod W.unop V ⟶ U =>
          prod.map f.unop (𝟙 V) ≫ g)
      map_id := by
        intro W
        apply ConcreteCategory.hom_ext
        intro g
        change prod.map (𝟙 W.unop) (𝟙 V) ≫ g = g
        rw [prod.map_id_id]
        simp
      map_comp := by
        intro W W' W'' f g
        apply TypeCat.homEquiv.injective
        funext h
        change
          prod.map (g.unop ≫ f.unop) (𝟙 V) ≫ h =
            prod.map g.unop (𝟙 V) ≫ prod.map f.unop (𝟙 V) ≫ h
        rw [← Category.comp_id (𝟙 V), ← prod.map_map]
        simp }

theorem internalHomFunctor_obj
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C) (W : SimplicialObject C) :
    (internalHomFunctor hC V U).obj (op W) =
      (simplicialProduct hC W V ⟶ U) :=
  rfl

/-! ## Representability and the internal hom object -/

/-- The chosen object and representation data for the source's internal hom. -/
structure InternalHomData
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C) where
  object : SimplicialObject C
  representation :
    (internalHomFunctor hC V U).RepresentableBy object

/-- The assertion that the source's internal hom of `V` into `U` exists. -/
abbrev HasInternalHom
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C) : Prop :=
  Nonempty (InternalHomData hC V U)

/-- A chosen simplicial object representing `W ↦ Hom(W × V, U)`. -/
noncomputable def internalHom
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C)
    (h : HasInternalHom hC V U) : SimplicialObject C :=
  (Classical.choice h).object

/-- The representing equivalence associated to the chosen internal hom. -/
noncomputable def internalHomRepresentation
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C)
    (h : HasInternalHom hC V U) :
    (internalHomFunctor hC V U).RepresentableBy
      (internalHom hC V U h) :=
  (Classical.choice h).representation

/-- The source's mapping property, with the product of simplicial objects explicit. -/
noncomputable def internalHomHomEquiv
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyProducts C)
    (V U : SimplicialObject C)
    (h : HasInternalHom hC V U) (W : SimplicialObject C) :
    (W ⟶ internalHom hC V U h) ≃
      (simplicialProduct hC W V ⟶ U) :=
  internalHomRepresentation hC V U h |>.homEquiv

/-! ## The simplex products used in the displayed degree formula -/

/-- The degreewise coproduct data for `Δ[n] × V`. -/
theorem standardSimplexCoproducts
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyCoproducts C)
    (n : ℕ) (V : SimplicialObject C) :
    Unit13.HasDegreewiseCoproducts (Δ[n] : SSet.{u}) V := by
  let hBin : HasBinaryCoproducts C :=
    hasBinaryCoproducts_of_hasFiniteNonemptyCoproducts hC
  exact @Unit13.degreewiseCoproductInstance C inferInstance hBin
    (Δ[n] : SSet.{u}) V
    (Unit13.standardSimplex_finite_nonempty n)

/-- The earlier chapter's coproduct-based product `Δ[n] × V`. -/
noncomputable def simplexProduct
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyCoproducts C)
    (n : ℕ) (V : SimplicialObject C) : SimplicialObject C :=
  Unit13.simplicialSetProductOf (Δ[n] : SSet.{u}) V
    (standardSimplexCoproducts hC n V)

/-- The earlier chapter's object `X × Δ[n]`, with `X` viewed as constant. -/
noncomputable def constantObjectProductWithSimplex
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyCoproducts C) (X : C) (n : ℕ) :
    SimplicialObject C :=
  simplexProduct hC n ((SimplicialObject.const C).obj X)

/-- Maps from the coproduct-based `X × Δ[n]` are maps from `X` in degree `n`. -/
noncomputable def constantObjectProductWithSimplexHomEquiv
    {C : Type u} [Category.{v} C]
    (hC : HasFiniteNonemptyCoproducts C) (X : C) (n : ℕ)
    (W : SimplicialObject C) :
    (constantObjectProductWithSimplex hC X n ⟶ W) ≃
      (X ⟶ W.obj (op (SimplexCategory.mk n))) := by
  simpa [constantObjectProductWithSimplex, simplexProduct,
    Unit13.constantObjectProductWithSimplexOf] using
    (Unit13.constantObjectProductWithSimplexOf_hom_equiv X n
      (standardSimplexCoproducts hC n ((SimplicialObject.const C).obj X)) W)

/-! ## The four source-facing hom-set identifications -/

/-- The first equality in the source's displayed chain, in the usable direction. -/
noncomputable def internalHomDegreeHomEquiv
    {C : Type u} [Category.{v} C]
    (hP : HasFiniteNonemptyProducts C)
    (hCop : HasFiniteNonemptyCoproducts C)
    (V U : SimplicialObject C)
    (hVU : HasInternalHom hP V U) (X : C) (n : ℕ) :
    (X ⟶ (internalHom hP V U hVU).obj (op (SimplexCategory.mk n))) ≃
      (constantObjectProductWithSimplex hCop X n ⟶
        internalHom hP V U hVU) :=
  (constantObjectProductWithSimplexHomEquiv hCop X n
    (internalHom hP V U hVU)).symm

/-- The second equality in the source's chain, after applying representability. -/
noncomputable def internalHomDegreeProductHomEquiv
    {C : Type u} [Category.{v} C]
    (hP : HasFiniteNonemptyProducts C)
    (hCop : HasFiniteNonemptyCoproducts C)
    (V U : SimplicialObject C)
    (hVU : HasInternalHom hP V U) (X : C) (n : ℕ) :
    (constantObjectProductWithSimplex hCop X n ⟶
        internalHom hP V U hVU) ≃
      (simplicialProduct hP (constantObjectProductWithSimplex hCop X n) V ⟶ U) :=
  internalHomHomEquiv hP V U hVU
    (constantObjectProductWithSimplex hCop X n)

/-- The internal-hom mapping property for the object `Δ[n] × V`. -/
noncomputable def internalHomSimplexHomEquiv
    {C : Type u} [Category.{v} C]
    (hP : HasFiniteNonemptyProducts C)
    (hCop : HasFiniteNonemptyCoproducts C)
    (V U : SimplicialObject C)
    (n : ℕ) (hSimplex : HasInternalHom hP (simplexProduct hCop n V) U)
    (X : C) :
    ((SimplicialObject.const C).obj X ⟶
        internalHom hP (simplexProduct hCop n V) U hSimplex) ≃
      (simplicialProduct hP ((SimplicialObject.const C).obj X)
        (simplexProduct hCop n V) ⟶ U) :=
  internalHomHomEquiv hP (simplexProduct hCop n V) U hSimplex
    ((SimplicialObject.const C).obj X)

/-- The last equality in the source's displayed chain, in the usable direction. -/
noncomputable def constantSimplicialObjectHomEquiv
    {C : Type u} [Category.{v} C] (X : C) (W : SimplicialObject C) :
    ((SimplicialObject.const C).obj X ⟶ W) ≃
      (X ⟶ W.obj (op (SimplexCategory.mk 0))) :=
  Unit13.constant_simplicial_object_hom_equiv X W

/-! ## The proposed degreewise construction target -/

/-- The object `Hom(Δ[n] × V, U)_0` proposed by the source as a degreewise
construction target for `Hom(V,U)`. -/
noncomputable def internalHomDegreeCandidate
    {C : Type u} [Category.{v} C]
    (hP : HasFiniteNonemptyProducts C)
    (hCop : HasFiniteNonemptyCoproducts C)
    (V U : SimplicialObject C)
    (n : ℕ) (hSimplex : HasInternalHom hP (simplexProduct hCop n V) U) : C :=
  (internalHom hP (simplexProduct hCop n V) U hSimplex).obj
    (op (SimplexCategory.mk 0))

/-- The candidate's functor-of-points mapping property, combining the last two
source identifications. -/
noncomputable def internalHomDegreeCandidateHomEquiv
    {C : Type u} [Category.{v} C]
    (hP : HasFiniteNonemptyProducts C)
    (hCop : HasFiniteNonemptyCoproducts C)
    (V U : SimplicialObject C)
    (n : ℕ) (hSimplex : HasInternalHom hP (simplexProduct hCop n V) U)
    (X : C) :
    (X ⟶ internalHomDegreeCandidate hP hCop V U n hSimplex) ≃
      (simplicialProduct hP ((SimplicialObject.const C).obj X)
        (simplexProduct hCop n V) ⟶ U) := by
    exact
    (constantSimplicialObjectHomEquiv X
      (internalHom hP (simplexProduct hCop n V) U hSimplex)).symm.trans
      (internalHomSimplexHomEquiv hP hCop V U n hSimplex X)

/-!
The first and last equivalences above are the earlier chapter's
`lemma-morphism-from-coproduct`.  The two middle equivalences are the
representability statements.  The source writes the two middle objects with
the same unparenthesized expression; without an additional comparison between
the two product constructions, the displayed chain is best used through the
separate canonical equivalences above.
-/

end Formalization.Books.Simplicial.Unit16
