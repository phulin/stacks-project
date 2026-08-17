import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# Simplicial Methods, Chapter 11: Simplicial sets

The source's simplicial sets are Mathlib's `SSet`, namely the category of
`Type`-valued presheaves on `SimplexCategory`.  The source's face and
degeneracy maps are the canonical `SimplicialObject.δ` and
`SimplicialObject.σ` families.  A simplex in degree `n` is therefore simply
an element of `U _⦋n⦌`.

Mathlib's `SSet.degenerate` is defined using maps from a lower-dimensional
simplex, and `SSet.degenerate_eq_iUnion_range_σ` identifies it with the
source's one-step degeneracies.  We use that canonical definition rather than
introducing a parallel predicate.
-/

namespace Formalization.Books.Simplicial.Unit11

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped _root_.Simplicial

universe u

/-! ## Terminology and the standard simplex -/

/-
The source's terminology is represented directly by the existing types and
maps: `x : U _⦋n⦌` is an `n`-simplex, `U.δ i x` is its `i`th face, and
`U.σ i x` is its `i`th degeneracy.  The next theorem records the source's
definition of degeneracy in the exact one-step form.
-/

theorem mem_degenerate_iff_exists_degeneracy
    {U : SSet.{u}} {n : ℕ} (x : U _⦋n + 1⦌) :
    x ∈ U.degenerate (n + 1) ↔
      ∃ i : Fin (n + 1), ∃ y : U _⦋n⦌, U.σ i y = x := by
  rw [SSet.degenerate_eq_iUnion_range_σ]
  simp only [Set.mem_iUnion, Set.mem_range]

/-!
`SSet.stdSimplex` is the canonical cosimplicial object whose value at
`[n]` is the source's `Δ[n]`.  Its object equivalence and map formula make
the source's definition by ordered maps explicit.
-/

def standard_simplex_obj_equiv (n m : ℕ) :
    (Δ[n] : SSet.{u}) _⦋m⦌ ≃
      (SimplexCategory.mk m ⟶ SimplexCategory.mk n) :=
  SSet.stdSimplex.objEquiv

theorem standard_simplex_map_obj_equiv_symm
    {n k l : ℕ} (f : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (g : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    (Δ[n] : SSet.{u}).map f.op (SSet.stdSimplex.objEquiv.symm g) =
      SSet.stdSimplex.objEquiv.symm (f ≫ g) := by
  rfl

/-!
The following two statements are the source's assertions about degeneracies
of `Δ[n]`.  They are consequences of Mathlib's stronger dimension interface,
and the top-dimensional uniqueness statement is already available verbatim.
-/

theorem standard_simplex_all_simplices_degenerate_of_gt
    {n m : ℕ} (h : n < m) (x : (Δ[n] : SSet.{u}) _⦋m⦌) :
    x ∈ (Δ[n] : SSet.{u}).degenerate m := by
  rw [SSet.degenerate_eq_univ_of_hasDimensionLT
    (Δ[n] : SSet.{u}) (n + 1) m (Nat.succ_le_of_lt h)]
  trivial

theorem standard_simplex_nonDegenerate_empty_of_gt
    {n m : ℕ} (h : n < m) :
    (Δ[n] : SSet.{u}).nonDegenerate m = ∅ :=
  SSet.nonDegenerate_eq_empty_of_hasDimensionLT
    (Δ[n] : SSet.{u}) (n + 1) m (Nat.succ_le_of_lt h)

theorem standard_simplex_unique_nonDegenerate_top (n : ℕ) :
    (Δ[n] : SSet.{u}).nonDegenerate n =
      {SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))} :=
  SSet.stdSimplex.nonDegenerate_top_dim n

/-! ## Maps out of a standard simplex -/

/-!
The source's canonical bijection is Mathlib's `SSet.yonedaEquiv`.  It sends
a map to its value on the canonical identity simplex, which is the unique
nondegenerate top-dimensional simplex above.
-/

def simplex_map_equiv (U : SSet.{u}) (n : ℕ) :
    (Δ[n] ⟶ U) ≃ U _⦋n⦌ :=
  SSet.yonedaEquiv

theorem simplex_map_equiv_apply (U : SSet.{u}) (n : ℕ)
    (f : Δ[n] ⟶ U) :
    SSet.yonedaEquiv f =
      f.app (op (SimplexCategory.mk n))
        (SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk n))) := by
  rfl

/-! ## The over-category example -/

/-!
The category `Δ/[n]` in the source is Mathlib's `Over [n]`, and its
projection to `Δ` is `Over.forget`.  The fibers are discrete and have the
expected simplex objects.  The category-theoretic content of the displayed
presheaf formula is the Yoneda equivalence `simplex_map_equiv` above.
-/

def simplexOverProjection (n : ℕ) :
    CategoryTheory.Over (SimplexCategory.mk n) ⥤ SimplexCategory :=
  CategoryTheory.Over.forget _

/-! The source's lift of `φ : [k] ⟶ [l]` at `ψ : [l] ⟶ [n]` has domain
`ψ ∘ φ`, which is the following canonical morphism in the over-category. -/

def simplexOverLift {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    CategoryTheory.Over.mk (φ ≫ ψ) ⟶ CategoryTheory.Over.mk ψ :=
  CategoryTheory.Over.homMk φ rfl

theorem simplexOverLift_projection {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    (simplexOverProjection n).map (simplexOverLift φ ψ) = φ := by
  rfl

theorem simplexOverLift_unique {n k l : ℕ}
    (φ : SimplexCategory.mk k ⟶ SimplexCategory.mk l)
    (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    ∃! χ : CategoryTheory.Over.mk (φ ≫ ψ) ⟶ CategoryTheory.Over.mk ψ,
      (simplexOverProjection n).map χ = φ := by
  refine ⟨simplexOverLift φ ψ, simplexOverLift_projection φ ψ, ?_⟩
  intro χ hχ
  apply CategoryTheory.Over.OverMorphism.ext
  exact hχ

instance simplexOverFiber_isDiscrete (n k : ℕ) :
    IsDiscrete (Functor.Fiber (simplexOverProjection n)
      (SimplexCategory.mk k)) := by
  sorry

theorem simplexOverFiber_object_description (n k : ℕ)
    (x : Functor.Fiber (simplexOverProjection n)
      (SimplexCategory.mk k)) :
    ∃ ψ : SimplexCategory.mk k ⟶ SimplexCategory.mk n,
      x.1 = CategoryTheory.Over.mk ψ := by
  sorry

theorem simplexOverFiber_objects (n k : ℕ) :
    Nonempty
      (Functor.Fiber (simplexOverProjection n) (SimplexCategory.mk k) ≃
        (Δ[n] : SSet.{u}) _⦋k⦌) := by
  sorry

/-! ## Products -/

/-!
For simplicial sets Mathlib's chosen categorical product is written `⊗`; its
degree-`n` object is the ordinary product `U _⦋n⦌ × V _⦋n⦌`.  This is the
canonical product used for the source's `U × V`.
-/

theorem product_hasDimensionLE
    (U V : SSet.{u}) (a b : ℕ)
    [U.HasDimensionLE a] [V.HasDimensionLE b] :
    (U ⊗ V).HasDimensionLE (a + b) := by
  infer_instance

theorem product_simplex_degenerate_of_gt
    (U V : SSet.{u}) (a b : ℕ)
    [U.HasDimensionLE a] [V.HasDimensionLE b]
    {n : ℕ} (h : a + b < n) (x : (U ⊗ V) _⦋n⦌) :
    x ∈ (U ⊗ V).degenerate n := by
  rw [SSet.degenerate_eq_univ_of_hasDimensionLT
    (U ⊗ V) (a + b + 1) n (Nat.succ_le_of_lt h)]
  trivial

end Formalization.Books.Simplicial.Unit11
