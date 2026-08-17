import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves

/-!
# Simplicial Methods, Chapter 5: Cosimplicial objects

The covariant functor-category interface for cosimplicial objects is already
provided by Mathlib.  This file records the source-facing interfaces and
examples, while reusing Mathlib's coface, codegeneracy, and generators-and-
relations APIs.
-/

namespace Formalization.Books.Simplicial.Unit05

open CategoryTheory
open CategoryTheory.Limits
open scoped _root_.Simplicial

universe v u

/-!
The source's cosimplicial object is Mathlib's `CosimplicialObject C`, namely a
covariant functor `SimplexCategory ⥤ C`.  Its category structure is the
functor-category structure, so a morphism is a natural transformation.  The
source's terms "cosimplicial set" and "cosimplicial abelian group" therefore
mean `CosimplicialObject (Type u)` and
`CosimplicialObject AddCommGrpCat`, respectively; no parallel aliases are
introduced.
-/

theorem cosimplicial_object_is_functor
    {C : Type u} [Category.{v} C] :
    CosimplicialObject C = (SimplexCategory ⥤ C) := rfl

theorem cosimplicial_morphism_is_natural_transformation
    {C : Type u} [Category.{v} C]
    (U U' : CosimplicialObject C) :
    (U ⟶ U') = NatTrans U U' := rfl

/-!
The objectwise and functorial assertions in the paragraph following the
definition are the ordinary functor laws.  We expose them in the notation of
the source.
-/

theorem cosimplicial_object_map_id
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C) (n : ℕ) :
    U.map (𝟙 (SimplexCategory.mk n)) =
      𝟙 (U ^⦋n⦌) := by
  exact U.map_id _

theorem cosimplicial_object_map_comp
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n m k : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k) :
    U.map (φ ≫ ψ) = U.map φ ≫ U.map ψ := by
  exact U.map_comp φ ψ

/-!
The source says that the induced maps are the unique map to degree zero and
the `n + 1` maps indexed by maps `[0] ⟶ [n]`.  For a general target category,
these are only distinguished maps induced by `Δ`; a functor does not make all
morphisms between its values unique or distinct.  The following two
declarations give the corrected, functorial form.
-/

theorem cosimplicial_object_map_to_zero_unique
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C) (n : ℕ)
    (f : SimplexCategory.mk n ⟶ SimplexCategory.mk 0) :
    U.map f = U.map (SimplexCategory.const (SimplexCategory.mk n)
      (SimplexCategory.mk 0) 0) := by
  rw [SimplexCategory.eq_const_to_zero f]

theorem cosimplicial_object_map_from_zero_indexed
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C) (n : ℕ)
    (f : SimplexCategory.mk 0 ⟶ SimplexCategory.mk n) :
    ∃ i : Fin (n + 1),
      U.map f = U.map (SimplexCategory.const (SimplexCategory.mk 0)
        (SimplexCategory.mk n) i) := by
  obtain ⟨i, rfl⟩ := SimplexCategory.exists_eq_const_of_zero f
  exact ⟨i, rfl⟩

/-!
For `U : CosimplicialObject C`, Mathlib's `U.δ` and `U.σ` are precisely the
source's coface and codegeneracy maps.  Their five displayed relations are
already proved in Mathlib, with `Fin` indices supplying the source bounds.
The wrappers below retain the source order and composition convention.
-/

theorem cosimplicial_coface_map
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) :
    U.δ i = U.map (SimplexCategory.δ i) := rfl

theorem cosimplicial_codegeneracy_map
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) :
    U.σ i = U.map (SimplexCategory.σ i) := rfl

theorem cosimplicial_coface_comp_coface
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    U.δ i ≫ U.δ j.succ = U.δ j ≫ U.δ (Fin.castSucc i) :=
  CosimplicialObject.δ_comp_δ U h

theorem cosimplicial_coface_comp_codegeneracy_of_le
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : i ≤ Fin.castSucc j) :
    U.δ (Fin.castSucc i) ≫ U.σ j.succ = U.σ j ≫ U.δ i :=
  CosimplicialObject.δ_comp_σ_of_le U h

theorem cosimplicial_coface_comp_codegeneracy_self
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i : Fin (n + 1)} :
    U.δ (Fin.castSucc i) ≫ U.σ i = 𝟙 _ :=
  CosimplicialObject.δ_comp_σ_self U

theorem cosimplicial_coface_comp_codegeneracy_succ
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i : Fin (n + 1)} :
    U.δ i.succ ≫ U.σ i = 𝟙 _ :=
  CosimplicialObject.δ_comp_σ_succ U

theorem cosimplicial_coface_comp_codegeneracy_of_gt
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)}
    (h : Fin.castSucc j < i) :
    U.δ i.succ ≫ U.σ (Fin.castSucc j) = U.σ j ≫ U.δ i :=
  CosimplicialObject.δ_comp_σ_of_gt U h

theorem cosimplicial_codegeneracy_comp_codegeneracy
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) :
    U.σ (Fin.castSucc i) ≫ U.σ j = U.σ j.succ ≫ U.σ i :=
  CosimplicialObject.σ_comp_σ U h

/-!
The converse characterization in the source is the generators-and-relations
presentation of `SimplexCategory` from Chapter 2: a functor out of the
presentation is determined by the generator images satisfying its relations,
and `Formalization.Books.Simplicial.Unit02.toSimplexCategory_is_equivalence`
identifies that presentation with `SimplexCategory`.  The canonical Mathlib
functor category and its identities are used here instead of introducing a
second sequence structure with duplicated typed relations.

Likewise, a morphism of cosimplicial objects is a natural transformation.  Its
componentwise characterization and commutation with cofaces and codegeneracies
are the following existing interfaces.
-/

theorem cosimplicial_morphism_ext
    {C : Type u} [Category.{v} C] {U U' : CosimplicialObject C}
    (f g : U ⟶ U')
    (h : ∀ n : SimplexCategory, f.app n = g.app n) :
    f = g :=
  CosimplicialObject.hom_ext f g h

theorem cosimplicial_morphism_coface_naturality
    {C : Type u} [Category.{v} C] {U U' : CosimplicialObject C}
    (f : U ⟶ U') {n : ℕ} (i : Fin (n + 2)) :
    U.δ i ≫ f.app (SimplexCategory.mk (n + 1)) =
      f.app (SimplexCategory.mk n) ≫ U'.δ i :=
  CosimplicialObject.δ_naturality f i

theorem cosimplicial_morphism_codegeneracy_naturality
    {C : Type u} [Category.{v} C] {U U' : CosimplicialObject C}
    (f : U ⟶ U') {n : ℕ} (i : Fin (n + 1)) :
    U.σ i ≫ f.app (SimplexCategory.mk n) =
      f.app (SimplexCategory.mk (n + 1)) ≫ U'.σ i :=
  CosimplicialObject.σ_naturality f i

/-!
The low-dimensional diagram in the source is just the degree `2`--`1`--`0`
part of `U.δ` and `U.σ`.  The source's subsequent list labels the three maps
`U _⦋2⦌ ⟶ U _⦋3⦌` as `δ^2_j`; with the source's own convention they are
`δ^3_j`, and the canonical indexed API has that corrected typing.
-/

/-!
The constant example is Mathlib's `CosimplicialObject.const`.
-/

theorem constant_cosimplicial_object_obj
    {C : Type u} [Category.{v} C] (X : C) (n : ℕ) :
    ((CosimplicialObject.const C).obj X).obj (SimplexCategory.mk n) = X := by
  rfl

theorem constant_cosimplicial_object_map
    {C : Type u} [Category.{v} C] (X : C)
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ((CosimplicialObject.const C).obj X).map φ = 𝟙 X := by
  rfl

/-!
The pushout example is Mathlib's Čech conerve.  For an arrow `f : X ⟶ Y`,
`Arrow.cechConerve` uses the chosen wide pushout of the family of `n + 1`
copies of `Y` over `X`; its map is the coordinate map induced by the order
map.  This is exactly the source construction, with coherent chosen
pushouts made explicit by the typeclass hypothesis.
-/

theorem pushout_cosimplicial_object_degree
    {C : Type u} [Category.{v} C] (f : Arrow C)
    [∀ n : ℕ, HasWidePushout f.left
      (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom)] (n : ℕ) :
    f.cechConerve.obj (SimplexCategory.mk n) =
      widePushout f.left (fun _ : Fin (n + 1) => f.right) (fun _ => f.hom) := by
  rfl

/-!
For every `n`, the source's `C[n]` is the representable covariant functor
`Hom([n], -)`, i.e. the coyoneda functor evaluated at `[n]`.
-/

def simplex_cosimplicial_set (n : ℕ) : CosimplicialObject (Type) :=
  CategoryTheory.coyoneda.obj (Opposite.op (SimplexCategory.mk n))

theorem simplex_cosimplicial_set_obj (n k : ℕ) :
    (simplex_cosimplicial_set n).obj (SimplexCategory.mk k) =
      (SimplexCategory.mk n ⟶ SimplexCategory.mk k) := rfl

/-!
Every coface is a split monomorphism.  The retraction is the corresponding
codegeneracy; `Fin.lastCases` packages the two source identities
`δ_i ≫ σ_i = 𝟙` and `δ_{i+1} ≫ σ_i = 𝟙` into one definition.
-/

def coface_split_mono
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) : SplitMono (U.δ i) where
  retraction := by
    induction i using Fin.lastCases with
    | last => exact U.σ (Fin.last n)
    | cast i => exact U.σ i
  id := by
    cases i using Fin.lastCases
    · simp only [Fin.lastCases_last]
      simpa using (CosimplicialObject.δ_comp_σ_succ U (i := Fin.last n))
    · simp only [Fin.lastCases_castSucc]
      exact CosimplicialObject.δ_comp_σ_self U

instance coface_is_split_mono
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) : IsSplitMono (U.δ i) :=
  IsSplitMono.mk' (coface_split_mono U i)

theorem coface_mono
    {C : Type u} [Category.{v} C] (U : CosimplicialObject C)
    {n : ℕ} (i : Fin (n + 2)) : Mono (U.δ i) := by
  infer_instance

end Formalization.Books.Simplicial.Unit05
