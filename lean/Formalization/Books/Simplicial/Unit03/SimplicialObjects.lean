import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.CategoryTheory.EpiMono
import Formalization.Books.Simplicial.Unit02.FiniteOrderedSets

/-!
# Simplicial Methods, Chapter 3: Simplicial objects

The canonical functor-category interface for simplicial objects is already in
Mathlib.  This file records the source-facing interfaces and points to the
existing face, degeneracy, generators-and-relations, and Čech-nerve APIs.
-/

namespace Formalization.Books.Simplicial.Unit03

open CategoryTheory
open CategoryTheory.Limits
open scoped _root_.Simplicial

universe v u

/-!
The source's simplicial object in `C` is Mathlib's
`CategoryTheory.SimplicialObject C`, namely a functor
`SimplexCategoryᵒᵖ ⥤ C`.  Its category structure is the functor-category
structure, so a morphism of simplicial objects is a natural transformation
and `SimplicialObject C` is the source's `Simp(C)`.

The source's simplicial sets are `SSet`, which is the existing abbreviation
`SimplicialObject (Type u)`.  Simplicial abelian groups are represented by
`SimplicialObject (AddCommGrpCat.{u})`, using Mathlib's bundled category of
abelian groups.  No parallel aliases are needed: these are exactly the
existing target categories of `SimplicialObject`.

For `X : SimplicialObject C`, the notation `X _⦋n⦌` is its value on `[n]`.
The definitions `SimplicialObject.δ` and `SimplicialObject.σ` are the source's
face and degeneracy maps, with the contravariant direction built into their
types.
-/

theorem simplicial_object_map_id
    {C : Type u} [Category.{v} C] (X : SimplicialObject C) (n : ℕ) :
    X.map ((𝟙 (SimplexCategory.mk n)).op) =
      𝟙 (X.obj (Opposite.op (SimplexCategory.mk n))) := by
  simp

theorem simplicial_object_map_comp
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n m k : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m)
    (ψ : SimplexCategory.mk m ⟶ SimplexCategory.mk k) :
    X.map ((φ ≫ ψ).op) = X.map ψ.op ≫ X.map φ.op := by
  simp

/-!
The source's nearby claim that these induced maps are all the morphisms in
the corresponding hom-sets is not asserted here: a functor selects morphisms
in `C` and does not generally control every morphism of `C` between its values.
The source-facing correction is to read those maps as distinguished maps
induced by the maps in `Δ`.
-/

/-!
The five opposite simplicial identities in the source are already available
in their fully typed form for every `X`:

* `SimplicialObject.δ_comp_δ` is the face-face relation;
* `SimplicialObject.δ_comp_σ_of_le` is the first face-degeneracy relation;
* `SimplicialObject.δ_comp_σ_self` and
  `SimplicialObject.δ_comp_σ_succ` are the two identity cases;
* `SimplicialObject.δ_comp_σ_of_gt` is the remaining face-degeneracy
  relation; and
* `SimplicialObject.σ_comp_σ` is the degeneracy-degeneracy relation.

Their `Fin` indices express exactly the source bounds, while categorical
composition `≫` is the opposite of the source's right-to-left notation.
The unindexed remark in the source is only an abbreviation of these same
declarations.

The converse characterization is represented by the canonical
`SimplexCategoryGenRel` presentation and
`Formalization.Books.Simplicial.Unit02.toSimplexCategory_is_equivalence`.
That presentation supplies the generators and relations needed to reconstruct
the unique functor; introducing a second sequence structure here would
duplicate the established interface.
-/

theorem simplicial_morphism_face_naturality
    {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}
    (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (Opposite.op (SimplexCategory.mk n)) =
      f.app (Opposite.op (SimplexCategory.mk (n + 1))) ≫ Y.δ i :=
  SimplicialObject.δ_naturality f i

theorem simplicial_morphism_degeneracy_naturality
    {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}
    (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (Opposite.op (SimplexCategory.mk (n + 1))) =
      f.app (Opposite.op (SimplexCategory.mk n)) ≫ Y.σ i :=
  SimplicialObject.σ_naturality f i

theorem simplicial_morphism_ext
    {C : Type u} [Category.{v} C] {X Y : SimplicialObject C}
    (f g : X ⟶ Y)
    (h : ∀ n : SimplexCategoryᵒᵖ, f.app n = g.app n) :
    f = g :=
  SimplicialObject.hom_ext f g h

/-!
The low-dimensional incidence data in the source is the corresponding
specialization of `X.δ` and `X.σ`: `X.σ ⟨0, ...⟩` is `s^0_0`, the two maps
`X.δ : X _⦋1⦌ ⟶ X _⦋0⦌` are `d^1_0,d^1_1`, and the two maps
`X.σ : X _⦋1⦌ ⟶ X _⦋2⦌` are `s^1_0,s^1_1`.  The displayed diagram is
therefore the degree `2`--`1`--`0` part of these canonical families; no
second diagrammatic structure is introduced.

The source's subsequent list has an index typo: its three maps labelled
`d^2_j = U(δ^2_j)` have type `U _⦋2⦌ ⟶ U _⦋1⦌`, whereas maps
`U _⦋3⦌ ⟶ U _⦋2⦌` are `d^3_j = U(δ^3_j)`.  The canonical indexed API uses
the latter typing.
-/

/-!
The constant example is Mathlib's existing constant simplicial-object
functor.  The following declarations expose its object and map components
in the notation used by the source.
-/

theorem constant_simplicial_object_obj
    {C : Type u} [Category.{v} C] (X : C) (n : ℕ) :
    ((SimplicialObject.const C).obj X).obj
        (Opposite.op (SimplexCategory.mk n)) = X := by
  rfl

theorem constant_simplicial_object_map
    {C : Type u} [Category.{v} C] (X : C)
    {n m : ℕ} (φ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) :
    ((SimplicialObject.const C).obj X).map φ.op = 𝟙 X := by
  rfl

/-!
The fibre-product example is Mathlib's canonical Čech nerve.  For an arrow
`f : Y ⟶ X`, `Arrow.cechNerve` uses the chosen wide pullback of the family of
`n + 1` copies of `Y` over `X`; its `map` is defined by
`WidePullback.lift` and the coordinate projections indexed by the underlying
order map.  Thus it is the source's coordinate formula, with the necessary
coherent choices of wide pullbacks made explicit by the typeclass hypotheses.
The source's geometric interpretation of faces as projections (forgetting a
coordinate) and degeneracies as diagonal maps (repeating a coordinate) is
the corresponding interpretation of the wide-pullback projections and the
coordinate-indexed lifts in this construction; it is explanatory rather than
a second definition.
-/

theorem cech_nerve_degree
    {C : Type u} [Category.{v} C] (f : Arrow C)
    [∀ n : ℕ, HasWidePullback f.right
      (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom)] (n : ℕ) :
    f.cechNerve.obj (Opposite.op (SimplexCategory.mk n)) =
      widePullback f.right (fun _ : Fin (n + 1) => f.left) (fun _ => f.hom) := by
  rfl

/-!
The source's final lemma is an immediate split-monomorphism statement.  The
canonical retraction of `X.σ i` is `X.δ (Fin.castSucc i)`, and the existing
identity `SimplicialObject.δ_comp_σ_self` supplies its real proof.
-/

def degeneracy_split_mono
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) : SplitMono (X.σ i) where
  retraction := X.δ (Fin.castSucc i)
  id := by
    exact SimplicialObject.δ_comp_σ_self X

instance degeneracy_is_split_mono
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) : IsSplitMono (X.σ i) :=
  IsSplitMono.mk' (degeneracy_split_mono X i)

theorem degeneracy_mono
    {C : Type u} [Category.{v} C] (X : SimplicialObject C)
    {n : ℕ} (i : Fin (n + 1)) : Mono (X.σ i) := by
  infer_instance

end Formalization.Books.Simplicial.Unit03
