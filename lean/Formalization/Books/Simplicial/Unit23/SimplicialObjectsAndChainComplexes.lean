import Formalization.Books.Simplicial.Unit22.SimplicialObjectsInAbelianCategories
import Formalization.Books.Homology.Unit13.Complexes
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Simplicial Methods, Chapter 23: Simplicial objects and chain complexes

The source's `Ch_{≥ 0}(𝒜)` is represented by Mathlib's canonical
`ChainComplex 𝒜 ℕ`.  This is the concrete nonnegative-index model of the
full subcategory of integer-indexed chain complexes used in the Homology
chapter; it keeps the degree formula `s(U).X n = U _⦋n⦌` definitionally
visible.  Normalized terms and degenerate terms use the normalized subobjects
and last-face factorization from Chapter 18.
-/

noncomputable section

namespace Formalization.Books.Simplicial.Unit23

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Simplicial.Unit18
open Formalization.Books.Simplicial.Unit22
open Opposite
open HomologicalComplex
open scoped _root_.Simplicial
open scoped ZeroObject

universe v u

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

/-! ## The associated (Moore) chain complex -/

/-- The alternating boundary in degree `n+1` of a simplicial object. -/
def associatedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    U.obj (op ⦋n + 1⦌) ⟶ U.obj (op ⦋n⦌) :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • U.δ i

/- The displayed cancellation identity in the source is the only
   proposition needed to build the complex; its proof is the standard
   face-face cancellation. -/
theorem associatedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    associatedBoundary U (n + 1) ≫ associatedBoundary U n = 0 := by
  sorry

/-- The associated nonnegative chain complex `s(U)` (the Moore complex). -/
noncomputable def associatedChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => U.obj (op ⦋n⦌))
    (associatedBoundary U)
    (associatedBoundary_comp U)

@[simp]
theorem associatedChainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (associatedChainComplex U).X n = U.obj (op ⦋n⦌) :=
  rfl

@[simp]
theorem associatedChainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (associatedChainComplex U).d (n + 1) n = associatedBoundary U n :=
  by simp [associatedChainComplex]

theorem associatedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    f.app (op ⦋n + 1⦌) ≫ associatedBoundary V n =
      associatedBoundary U n ≫ f.app (op ⦋n⦌) := by
  sorry

theorem associatedChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      f.app (op ⦋i⦌) ≫ (associatedChainComplex V).d i j =
        (associatedChainComplex U).d i j ≫ f.app (op ⦋j⦌) := by
  sorry

/-- The chain map induced by a morphism of simplicial objects. -/
def associatedChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    associatedChainComplex U ⟶ associatedChainComplex V :=
  { f := fun n => f.app (op ⦋n⦌)
    comm' := associatedChainComplexMap_comm f }

@[simp]
theorem associatedChainComplexMap_f
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (associatedChainComplexMap f).f n = f.app (op ⦋n⦌) :=
  rfl

/-- The functor `s : Simp(𝒜) ⥤ Ch_{≥0}(𝒜)`. -/
def associatedChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := associatedChainComplex U
  map f := associatedChainComplexMap f
  map_id U := by
    ext n
    rfl
  map_comp f g := by
    ext n
    rfl

theorem associatedChainComplexFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (SimplicialObject C) (ChainComplex C ℕ)
      (associatedChainComplexFunctor C) := by
  sorry

/-! ## The extension and Eilenberg--Mac Lane homology statements -/

/-- The source's extension object between consecutive Eilenberg--Mac Lane
objects, using the canonical Chapter 22 interface. -/
abbrev eilenbergMacLaneExtension
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) : SimplicialObject C :=
  extensionObject A k

theorem eilenbergMacLaneExtension_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    (associatedChainComplex (eilenbergMacLaneExtension A k)).Acyclic := by
  sorry

/- The textbook says only "integer" in the next two lemmas, while its
   definition of `K(A,k)` has the necessary hypothesis `k ≥ 0`.  The natural
   Lean interface therefore uses `k : ℕ`. -/
theorem eilenbergMacLane_homology_at
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    Nonempty ((associatedChainComplex (eilenbergMacLane A k)).homology k ≅ A) := by
  sorry

theorem eilenbergMacLane_homology_vanishes
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k i : ℕ) (hi : i ≠ k) :
    IsZero ((associatedChainComplex (eilenbergMacLane A k)).homology i) := by
  sorry

/-! ## The normalized chain complex -/

/-- The signed last-face differential on normalized terms. -/
def normalizedBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedObject U (n + 1) ⟶ normalizedObject U n :=
  (-1 : ℤ) ^ (n + 1) • normalizedLastFace U n

theorem normalizedBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    normalizedBoundary U (n + 1) ≫ normalizedBoundary U n = 0 := by
  sorry

/-- The normalized chain complex `N(U)`. -/
noncomputable def normalizedChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => normalizedObject U n)
    (normalizedBoundary U)
    (normalizedBoundary_comp U)

@[simp]
theorem normalizedChainComplex_X
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedChainComplex U).X n = normalizedObject U n :=
  rfl

@[simp]
theorem normalizedChainComplex_d
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedChainComplex U).d (n + 1) n = normalizedBoundary U n :=
  by simp [normalizedChainComplex]

theorem normalizedBoundary_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    normalizedSubobjectMap f (n + 1) ≫ normalizedBoundary V n =
      normalizedBoundary U n ≫ normalizedSubobjectMap f n := by
  sorry

theorem normalizedChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      normalizedSubobjectMap f i ≫ (normalizedChainComplex V).d i j =
        (normalizedChainComplex U).d i j ≫ normalizedSubobjectMap f j := by
  sorry

/-- The chain map induced on normalized complexes. -/
def normalizedChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    normalizedChainComplex U ⟶ normalizedChainComplex V :=
  { f := fun n => normalizedSubobjectMap f n
    comm' := normalizedChainComplexMap_comm f }

def normalizedChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := normalizedChainComplex U
  map f := normalizedChainComplexMap f
  map_id U := by
    ext n
    exact normalizedSubobjectMap_id U n
  map_comp f g := by
    ext n
    exact normalizedSubobjectMap_comp f g n

theorem normalizedChainComplexFunctor_exact
    {C : Type u} [Category.{v} C] [Abelian C] :
    exactFunctor (SimplicialObject C) (ChainComplex C ℕ)
      (normalizedChainComplexFunctor C) := by
  sorry

/-! ## The canonical map from normalized to associated complexes -/

theorem normalized_to_associated_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      (normalizedSubobject U i).arrow ≫ (associatedChainComplex U).d i j =
        (normalizedChainComplex U).d i j ≫
          (normalizedSubobject U j).arrow := by
  sorry

/-- The canonical inclusion `N(U) ⟶ s(U)`. -/
def normalizedToAssociated
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    normalizedChainComplex U ⟶ associatedChainComplex U :=
  { f := fun n => (normalizedSubobject U n).arrow
    comm' := normalized_to_associated_comm U }

theorem normalizedToAssociated_component
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (normalizedToAssociated U).f n = (normalizedSubobject U n).arrow :=
  rfl

theorem normalized_eilenbergMacLane_at
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k : ℕ) :
    Nonempty (normalizedObject (eilenbergMacLane A k) k ≅ A) := by
  sorry

theorem normalized_eilenbergMacLane_vanishes
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : C) (k i : ℕ) (hi : i ≠ k) :
    IsZero (normalizedObject (eilenbergMacLane A k) i) := by
  sorry

theorem normalizedToAssociated_split
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsSplitMono (normalizedToAssociated U) := by
  sorry

/-! ## The degenerate subcomplex and the splitting -/

/-- Indices for the source's direct sum of normalized terms mapping
surjectively into degree `n`. -/
abbrev DegenerateIndex (n : ℕ) :=
  Σ m : Fin n, SurjectiveSimplexIndex n m.1

noncomputable instance degenerateIndexFintype (n : ℕ) :
    Fintype (DegenerateIndex n) := Fintype.ofFinite _

noncomputable def degenerateSummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  ∐ fun a : DegenerateIndex n => normalizedObject U a.1.1

noncomputable def degenerateSummandMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateSummand U n ⟶ U.obj (op ⦋n⦌) :=
  Sigma.desc (fun a =>
    (normalizedSubobject U a.1.1).arrow ≫ U.map a.2.1.op)

/- The image of the displayed direct-sum map is the source's `D(U)_n`. -/
noncomputable def degenerateSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : Subobject (U.obj (op ⦋n⦌)) :=
  imageSubobject (degenerateSummandMap U n)

noncomputable abbrev degenerateObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  degenerateSubobject U n

theorem degenerateBoundary_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors
      ((degenerateSubobject U (n + 1)).arrow ≫ associatedBoundary U n) := by
  sorry

noncomputable def degenerateBoundary
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateObject U (n + 1) ⟶ degenerateObject U n :=
  (degenerateSubobject U n).factorThru
    ((degenerateSubobject U (n + 1)).arrow ≫ associatedBoundary U n)
    (degenerateBoundary_factors U n)

theorem degenerateBoundary_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateBoundary U (n + 1) ≫ degenerateBoundary U n = 0 := by
  sorry

/-- The degenerate subcomplex `D(U) ⊂ s(U)`. -/
noncomputable def degenerateChainComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => degenerateObject U n)
    (degenerateBoundary U)
    (degenerateBoundary_comp U)

theorem degenerateSubobject_map_factors
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject V n).Factors
      ((degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌)) := by
  sorry

noncomputable def degenerateSubobjectMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    degenerateObject U n ⟶ degenerateObject V n :=
  (degenerateSubobject V n).factorThru
    ((degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌))
    (degenerateSubobject_map_factors f n)

theorem degenerateSubobjectMap_arrow
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    degenerateSubobjectMap f n ≫ (degenerateSubobject V n).arrow =
      (degenerateSubobject U n).arrow ≫ f.app (op ⦋n⦌) :=
  Subobject.factorThru_arrow _ _ _

theorem degenerateChainComplexMap_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    ∀ i j : ℕ, (ComplexShape.down ℕ).Rel i j →
      degenerateSubobjectMap f i ≫ (degenerateChainComplex V).d i j =
        (degenerateChainComplex U).d i j ≫ degenerateSubobjectMap f j := by
  sorry

noncomputable def degenerateChainComplexMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V : SimplicialObject C} (f : U ⟶ V) :
    degenerateChainComplex U ⟶ degenerateChainComplex V :=
  { f := fun n => degenerateSubobjectMap f n
    comm' := degenerateChainComplexMap_comm f }

theorem degenerateChainComplexMap_id
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    degenerateChainComplexMap (𝟙 U) = 𝟙 (degenerateChainComplex U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateSubobjectMap (𝟙 U) n = 𝟙 _
  apply (cancel_mono (degenerateSubobject U n).arrow).1
  rw [degenerateSubobjectMap_arrow]
  simp

theorem degenerateChainComplexMap_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    degenerateChainComplexMap (f ≫ g) =
      degenerateChainComplexMap f ≫ degenerateChainComplexMap g := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degenerateSubobjectMap (f ≫ g) n =
    degenerateSubobjectMap f n ≫ degenerateSubobjectMap g n
  apply (cancel_mono (degenerateSubobject W n).arrow).1
  rw [degenerateSubobjectMap_arrow]
  simp only [Category.assoc]
  rw [degenerateSubobjectMap_arrow]
  rw [← Category.assoc, degenerateSubobjectMap_arrow]
  simp [Category.assoc]

def degenerateChainComplexFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := degenerateChainComplex U
  map f := degenerateChainComplexMap f
  map_id U := by
    exact degenerateChainComplexMap_id U
  map_comp f g := by
    exact degenerateChainComplexMap_comp f g

/- The alternative source description uses all lower-degree terms rather than
   only normalized summands. -/
noncomputable def fullDegenerateSummand
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) : C :=
  ∐ fun a : DegenerateIndex n => U.obj (op ⦋a.1.1⦌)

noncomputable def fullDegenerateSummandMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    fullDegenerateSummand U n ⟶ U.obj (op ⦋n⦌) :=
  Sigma.desc (fun a => U.map a.2.1.op)

theorem degenerateSubobject_eq_full
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) (n : ℕ) :
    degenerateSubobject U n = imageSubobject (fullDegenerateSummandMap U n) := by
  sorry

/- In `AddCommGrpCat`, this equality is the categorical form of the source's
   statement that degenerate terms are sums of degenerate simplices. -/

theorem normalized_and_degenerate_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    Nonempty (associatedChainComplex U ≅
      normalizedChainComplex U ⊞ degenerateChainComplex U) := by
  sorry

theorem normalized_to_associated_is_split
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    IsSplitMono (normalizedToAssociated U) :=
  normalizedToAssociated_split U

theorem normalized_to_associated_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    QuasiIso (normalizedToAssociated U) := by
  sorry

theorem degenerateChainComplex_acyclic
    {C : Type u} [Category.{v} C] [Abelian C]
    (U : SimplicialObject C) :
    (degenerateChainComplex U).Acyclic := by
  sorry

end Formalization.Books.Simplicial.Unit23
