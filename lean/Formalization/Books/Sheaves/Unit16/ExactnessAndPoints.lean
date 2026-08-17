import Formalization.Books.Sheaves.Unit13.StalksOfPresheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 16: Exactness and points

The source span `books/sheaves.tex:1333--1457` is the section
`Exactness and points`.  The set-valued exactness criteria use Mathlib's
canonical sheaf and stalk APIs.  Subpresheaves are represented by
`CategoryTheory.Subfunctor`, and local surjectivity is Mathlib's canonical
`TopCat.Presheaf.IsLocallySurjective` predicate.

The final source lemma is stated for a category-valued sheaf and its
underlying sheaf of types.  The stalk maps are transported across the
canonical underlying-stalk isomorphisms from Chapter 13, so the hypothesis
that they are algebraic-structure morphisms has the source's precise type.
-/

namespace Formalization.Books.Sheaves.Unit16

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit13
open Formalization.Books.Sheaves.Unit15

universe u v

noncomputable section

/-! ## Points detect exactness for sheaves of sets -/

/-!
The following three statements are the three clauses of the source's first
lemma.  In each case the stalk map is the map induced by the canonical
`TopCat.Presheaf.stalkFunctor`.
-/

/-- A morphism of sheaves of sets is monic exactly when all stalk maps are injective. -/
theorem sheaf_mono_iff_stalk_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔
      ∀ x : X,
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  sorry

/-- A morphism of sheaves of sets is epic exactly when all stalk maps are surjective. -/
theorem sheaf_epi_iff_stalk_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔
      ∀ x : X,
        Function.Surjective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  sorry

/-- A morphism of sheaves of sets is an isomorphism exactly when all stalk maps are bijective. -/
theorem sheaf_isIso_iff_stalk_bijective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    IsIso φ ↔
      ∀ x : X,
        Function.Bijective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  sorry

/-! ## Injective, surjective, and subobject terminology -/

/-!
`Subfunctor` is Mathlib's literal family-of-subsets construction: its
`obj` fields are subsets of the ambient sections and its `map` field says
that restrictions preserve those subsets.  The relation below lets an
arbitrary presheaf be called a subpresheaf when it is naturally isomorphic
to such a subfunctor, which is invariant under the choice of section types.
-/

/-- A subpresheaf of a set-valued presheaf, represented by a subfunctor. -/
abbrev Subpresheaf {X : TopCat.{v}}
    (G : TopCat.Presheaf (Type v) X) : Type _ :=
  Subfunctor G

/-- A presheaf is a subpresheaf of another when it is isomorphic to a subfunctor of it. -/
def IsSubpresheaf {X : TopCat.{v}}
    (F G : TopCat.Presheaf (Type v) X) : Prop :=
  ∃ P : Subpresheaf G, Nonempty (F ≅ P.toFunctor)

/-- A subpresheaf whose source and ambient presheaves are sheaves is a subsheaf. -/
def IsSubsheaf {X : TopCat.{v}}
    (F G : TopCat.Presheaf (Type v) X) : Prop :=
  TopCat.Presheaf.IsSheaf F ∧ TopCat.Presheaf.IsSheaf G ∧ IsSubpresheaf F G

/-- A morphism of set-valued presheaves is injective on sections over every open. -/
def PresheafInjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  ∀ U : Opens X, Function.Injective (φ.app (op U))

/-- A morphism of set-valued presheaves is surjective on sections over every open. -/
def PresheafSurjective {X : TopCat.{v}}
    {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  ∀ U : Opens X, Function.Surjective (φ.app (op U))

/-- A morphism of sheaves of sets is injective in the source's sectionwise sense. -/
abbrev SheafInjective {X : TopCat.{v}}
    {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  PresheafInjective φ.hom

/-- A morphism of sheaves of sets is surjective in the source's local sense. -/
abbrev SheafSurjective {X : TopCat.{v}}
    {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) : Prop :=
  TopCat.Presheaf.IsLocallySurjective φ.hom

/-- The local-preimage formulation of the source's sheaf-surjectivity definition. -/
theorem sheafSurjective_iff_local_preimages
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafSurjective φ ↔
      ∀ (U : Opens X) (t : G.presheaf.obj (op U)), ∀ x ∈ U,
        ∃ (V : Opens X) (hVU : V ≤ U),
          (∃ s : F.presheaf.obj (op V),
            φ.hom.app (op V) s = G.presheaf.map (homOfLE hVU).op t) ∧ x ∈ V := by
  exact TopCat.Presheaf.isLocallySurjective_iff φ.hom

/-! ## Categorical epi/mono characterizations -/

/-- In the category of set-valued presheaves, epimorphisms are sectionwise surjective. -/
theorem presheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔ PresheafSurjective φ := by
  sorry

/-- In the category of set-valued presheaves, monomorphisms are sectionwise injective. -/
theorem presheaf_mono_iff_injective
    {X : TopCat.{v}} {F G : TopCat.Presheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔ PresheafInjective φ := by
  sorry

/-- In the category of sheaves of sets, epimorphisms are exactly the locally surjective maps. -/
theorem sheaf_epi_iff_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Epi φ ↔ SheafSurjective φ := by
  sorry

/-- In the category of sheaves of sets, monomorphisms are exactly the sectionwise injective maps. -/
theorem sheaf_mono_iff_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    Mono φ ↔ SheafInjective φ := by
  sorry

/-- Sectionwise injectivity of a sheaf map is equivalent to injectivity on all stalks. -/
theorem sheaf_injective_iff_stalk_injective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafInjective φ ↔
      ∀ x : X,
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  sorry

/-- Local surjectivity of a sheaf map is equivalent to surjectivity on all stalks. -/
theorem sheaf_surjective_iff_stalk_surjective
    {X : TopCat.{v}} {F G : TopCat.Sheaf (Type v) X} (φ : F ⟶ G) :
    SheafSurjective φ ↔
      ∀ x : X,
        Function.Surjective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  sorry

/-! ## Stalkwise algebraic-structure morphisms -/

/-!
For a category-valued sheaf, the stalk in `C` and the stalk of its
underlying presheaf of types are canonically isomorphic.  The next
definition transports an underlying stalk map to the categorical stalks.
-/

/-- The underlying sheaf of types associated to a `C`-valued sheaf. -/
noncomputable def underlyingSheaf
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) : TopCat.Sheaf (Type v) X :=
  ⟨underlyingPresheaf A F.presheaf,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp A F.presheaf).mp F.property⟩

/-- The underlying sheaf morphism induced by a morphism of `C`-valued sheaves. -/
def underlyingSheafMorphism
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X} (φ : F ⟶ G) :
    underlyingSheaf A F ⟶ underlyingSheaf A G :=
  ⟨underlyingPresheafMorphism A φ.hom⟩

/-- The map between categorical stalks induced by an underlying sheaf map. -/
noncomputable def underlyingStalkMap
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G) (x : X) :
    A.obj (algebraicStalk F.presheaf x) →
      A.obj (algebraicStalk G.presheaf x) :=
  fun s =>
    (algebraicStalkUnderlyingIso A G.presheaf x).toEquiv.symm
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom
        ((algebraicStalkUnderlyingIso A F.presheaf x).toEquiv s))

/-!
The displayed square in the source is represented by the following
section-to-stalks map and its naturality statement.  The codomain
`∀ x : U, ...` is the dependent product over the points of `U`.
-/

/-- The map from sections on an open to the product of the categorical stalks over its points. -/
noncomputable def algebraicSectionToStalks
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) (U : Opens X) :
    A.obj (F.presheaf.obj (op U)) →
      ∀ x : U, A.obj (algebraicStalk F.presheaf x.1) :=
  fun s x => A.map (algebraicStalkGerm F.presheaf U x.1 x.2) s

/-- Sections of a category-valued sheaf are determined by all their categorical stalks. -/
theorem algebraicSectionToStalks_injective
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    (F : TopCat.Sheaf C X) (U : Opens X) :
    Function.Injective (algebraicSectionToStalks A F U) := by
  sorry

/-- Naturality of the displayed section-to-stalks square. -/
theorem algebraicSectionToStalks_naturality
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G)
    (U : Opens X) (s : A.obj (F.presheaf.obj (op U))) :
    ∀ x : U,
      underlyingStalkMap A φ x.1
          (algebraicSectionToStalks A F U s x) =
        algebraicSectionToStalks A G U (φ.hom.app (op U) s) x := by
  sorry

/-- An underlying map is a morphism of sheaves of algebraic structures when it lifts to `C`. -/
def IsAlgebraicStructureSheafMorphism
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G) : Prop :=
  ∃ ψ : F ⟶ G, underlyingSheafMorphism A ψ = φ

/-- Stalkwise algebraic-structure morphisms lift an underlying sheaf map to `C`. -/
theorem isAlgebraicStructureSheafMorphism_of_stalkwise
    {C : Type u} [Category.{v} C] (A : C ⥤ Type v)
    [AlgebraicStructureType C A] {X : TopCat.{v}}
    {F G : TopCat.Sheaf C X}
    (φ : underlyingSheaf A F ⟶ underlyingSheaf A G)
    (hφ : ∀ x : X, IsAlgebraicStructureMorphism A (underlyingStalkMap A φ x)) :
    IsAlgebraicStructureSheafMorphism A φ := by
  sorry

end

end Formalization.Books.Sheaves.Unit16
