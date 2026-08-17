import Formalization.Books.Sheaves.Unit05.PresheavesOfAlgebraicStructures
import Formalization.Books.Sheaves.Unit09.SheavesOfAlgebraicStructures
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.MonCat.FilteredColimits
import Mathlib.Algebra.Category.MonCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Lie.Basic
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Sheaves on Spaces, Chapter 15: Algebraic structures

The source span `books/sheaves.tex:1177--1332` is the chapter's section
`Algebraic structures`.  The declarations below keep category-valued
presheaves canonical (`TopCat.Presheaf`) and express the source's underlying
set convention through the forgetful functor from Chapter 5.
-/

namespace Formalization.Books.Sheaves.Unit15

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit09

universe u v r k

noncomputable section

/-! ## Types of algebraic structures -/

/--
A category-valued functor is a type of algebraic structure when it has the
faithfulness, limit, filtered-colimit, and isomorphism-reflection properties
used throughout this section.
-/
class AlgebraicStructureType (C : Type u) [Category.{v} C]
    (F : C ⥤ Type v) : Prop extends
  F.Faithful,
  HasLimitsOfSize.{v, v} C,
  PreservesLimitsOfSize.{v, v} F,
  HasFilteredColimitsOfSize.{v, v} C,
  PreservesFilteredColimitsOfSize.{v, v} F,
  F.ReflectsIsomorphisms

/-!
The category of Lie algebras is not bundled in this Mathlib version.  The
small category below supplies the source-facing object and morphism types so
that the textbook's Lie-algebra example has a precise Lean interface.
-/

/-- The structure carried by an object of the fixed-field Lie-algebra category. -/
structure LieAlgebraObject (K : Type k) [Field K] (L : Type u) where
  lieRing : LieRing L
  lieAlgebra : @LieAlgebra K L _ lieRing

/-- The category of Lie algebras over a fixed field, with Lie homomorphisms. -/
structure LieAlgebraCat (K : Type k) [Field K] : Type (max k u + 1) where
  carrier : Type u
  structureData : LieAlgebraObject K carrier

namespace LieAlgebraCat

variable {K : Type k} [Field K]

instance : CoeSort (LieAlgebraCat K) (Type u) := ⟨LieAlgebraCat.carrier⟩

instance (X : LieAlgebraCat K) : LieRing (X : Type u) := X.structureData.lieRing

instance (X : LieAlgebraCat K) : LieAlgebra K (X : Type u) :=
  X.structureData.lieAlgebra

/-- Bundle an existing Lie algebra as an object. -/
def of (L : Type u) [LieRing L] [LieAlgebra K L] : LieAlgebraCat K :=
  ⟨L, { lieRing := inferInstance, lieAlgebra := inferInstance }⟩

/-- Morphisms in the fixed-field Lie-algebra category. -/
@[ext]
structure Hom (X Y : LieAlgebraCat K) where
  hom : (X : Type u) →ₗ⁅K⁆ (Y : Type u)

instance : Category (LieAlgebraCat K) where
  Hom := Hom
  id X := ⟨LieHom.id⟩
  comp f g := ⟨LieHom.comp g.hom f.hom⟩
  id_comp f := by
    apply Hom.ext
    exact LieHom.comp_id f.hom
  comp_id f := by
    apply Hom.ext
    exact LieHom.id_comp f.hom
  assoc f g h := by
    apply Hom.ext
    rfl

instance : ConcreteCategory (LieAlgebraCat K)
    (fun X Y => (X : Type u) →ₗ⁅K⁆ (Y : Type u)) where
  hom f := f.hom
  ofHom f := ⟨f⟩
  hom_ofHom _ := rfl
  ofHom_hom f := by cases f; rfl
  id_apply := by intro X x; rfl
  comp_apply := by intro X Y Z f g x; rfl

end LieAlgebraCat

/-!
The standard examples in the source use the canonical forgetful functors.
The theorem is left as an interface statement at this stage; its proof is
the routine verification of the listed Mathlib limit and filtered-colimit
instances (and the corresponding Lie-algebra constructions).
-/

/-- Pointed sets, abelian groups, groups, monoids, rings, modules, and Lie
algebras are types of algebraic structures in the sense above. -/
theorem standardAlgebraicStructureTypes :
    AlgebraicStructureType (Pointed.{u}) (forget Pointed) ∧
      AlgebraicStructureType (AddCommGrpCat.{u}) (forget AddCommGrpCat) ∧
      AlgebraicStructureType (GrpCat.{u}) (forget GrpCat) ∧
      AlgebraicStructureType (MonCat.{u}) (forget MonCat) ∧
      AlgebraicStructureType (RingCat.{u}) (forget RingCat) ∧
      (∀ (R : Type r) [Ring R],
        AlgebraicStructureType (ModuleCat.{u} R) (forget (ModuleCat.{u} R))) ∧
      (∀ (K : Type k) [Field K],
        AlgebraicStructureType (LieAlgebraCat.{u} K) (forget (LieAlgebraCat.{u} K))) := by
  sorry

/-! ## Consequences of the definition -/

/-- The source's terminal-object, product, pullback, equalizer, mono, epi,
and filtered-colimit consequences of being an algebraic structure type. -/
structure AlgebraicStructureProperties
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] : Prop where
  /-- A terminal object has a singleton underlying set. -/
  terminal :
    ∃ (zero : C), Nonempty (IsTerminal zero) ∧
      Nonempty (F.obj zero) ∧ Subsingleton (F.obj zero)
  /-- Products are computed by products of underlying sets. -/
  products :
    ∀ {ι : Type v} (A : ι → C),
      Nonempty
        (F.obj (limit (Discrete.functor A)) ≅
          limit (Discrete.functor (fun i => F.obj (A i))))
  /-- Fibre products are computed by fibre products of underlying sets. -/
  fibreProducts :
    ∀ {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B),
      Nonempty
        (F.obj (pullback f g) ≅ pullback (F.map f) (F.map g))
  /-- Equalizers are computed by equalizers of underlying sets. -/
  equalizers :
    ∀ {A B : C} (f g : A ⟶ B),
      Nonempty (IsLimit (F.mapCone (limit.cone (parallelPair f g))))
  /-- Monomorphisms are exactly the morphisms injective on underlying sets. -/
  monomorphisms :
    ∀ {A B : C} (f : A ⟶ B),
      Mono f ↔ Function.Injective (F.map f)
  /-- Surjectivity on underlying sets implies categorical epimorphy. -/
  epimorphisms :
    ∀ {A B : C} (f : A ⟶ B),
      Function.Surjective (F.map f) → Epi f
  /-- Filtered colimits are computed by filtered colimits of underlying sets. -/
  filteredColimits :
    ∀ {J : Type v} [Category.{v} J] [IsFiltered J] (D : J ⥤ C),
      Nonempty
        (F.obj (colimit D) ≅ colimit (D ⋙ F))

/-- The structural properties lemma from the source. -/
theorem algebraicStructureType_properties {C : Type u} [Category.{v} C]
    {F : C ⥤ Type v} [AlgebraicStructureType C F] :
    AlgebraicStructureProperties (C := C) (F := F) := by
  sorry

/-! ## Image containment and factorization -/

/-- An underlying image containment through an underlying injection lifts to a
factorization in the category of algebraic structures. -/
theorem factor_through_of_image_subset
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F]
    {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B)
    (hg : Function.Injective (F.map g))
    (himage : Set.range (F.map f) ⊆ Set.range (F.map g)) :
    ∃ t : A ⟶ C', t ≫ g = f := by
  sorry

/-! ## The commutative-square application -/

/-- The source's diagrammatic application of the image-containment lemma. -/
theorem exists_square_lift
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F]
    {A B C' D : C} (f : A ⟶ B) (g : B ⟶ D) (h : C' ⟶ D)
    (hh : Function.Injective (F.map h))
    (himage : Set.range (F.map (f ≫ g)) ⊆ Set.range (F.map h)) :
    ∃ k : A ⟶ C', k ≫ h = f ≫ g := by
  exact factor_through_of_image_subset (f ≫ g) h hh himage

/-! ## Pointwise products on a space -/

/-- The product object indexed by the points of an open. -/
noncomputable abbrev pointwiseProductObject
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) : C :=
  limit (Discrete.functor (fun x : U => A x))

/-- Restriction of a pointwise product along an inclusion of opens. -/
noncomputable def pointwiseProductRestriction
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) {U V : Opens X} (h : V ≤ U) :
    pointwiseProductObject (F := F) A U ⟶ pointwiseProductObject (F := F) A V :=
  limit.lift (Discrete.functor (fun x : V => A x))
    (Fan.mk _ fun x =>
        limit.π (Discrete.functor (fun x : U => A x))
        (Discrete.mk ⟨x, h x.property⟩))

theorem pointwiseProductRestriction_π
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) {U V : Opens X} (h : V ≤ U) (x : Discrete V) :
    pointwiseProductRestriction (F := F) A h ≫
        limit.π (Discrete.functor (fun x : V => A x)) x =
      limit.π (Discrete.functor (fun x : U => A x))
        (Discrete.mk ⟨x.as, h x.as.property⟩) := by
  unfold pointwiseProductRestriction pointwiseProductObject
  rw [limit.lift_π]
  rfl

/-- The category-valued pointwise product presheaf `U ↦ ∏ x ∈ U, A x`. -/
def pointwiseProductPresheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) : TopCat.Presheaf C X where
  obj U := pointwiseProductObject (F := F) A U.unop
  map {U V} f := pointwiseProductRestriction (F := F) A f.unop.le
  map_id U := by
    unfold pointwiseProductObject
    apply (limit.isLimit _).hom_ext
    intro x
    rw [limit.cone_π]
    rw [pointwiseProductRestriction_π]
    simp
  map_comp f g := by
    unfold pointwiseProductObject
    apply (limit.isLimit _).hom_ext
    intro x
    rw [limit.cone_π]
    rw [Category.assoc, pointwiseProductRestriction_π,
      pointwiseProductRestriction_π, pointwiseProductRestriction_π]

@[simp]
theorem pointwiseProductPresheaf_obj
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) :
    (pointwiseProductPresheaf (F := F) A).obj (op U) =
      pointwiseProductObject (F := F) A U :=
  rfl

/-- The underlying pointwise product has the expected product of underlying
sets on every open. -/
theorem pointwiseProductPresheaf_underlying_sections
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) (U : Opens X) :
    Nonempty
      (F.obj (pointwiseProductObject (F := F) A U) ≃
        ∀ x : U, F.obj (A x)) := by
  sorry

/-- A category-valued presheaf is a sheaf of algebraic structures in the
category-valued equalizer-of-products sense from Chapter 9. -/
abbrev IsSheafOfAlgebraicStructures
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (𝒜 : TopCat.Presheaf C X) : Prop :=
  CategoryValuedSheaf 𝒜

/-- For a type of algebraic structures, the category-valued sheaf condition
is equivalent to the sheaf condition on the underlying presheaf of sets. -/
theorem isSheafOfAlgebraicStructures_iff_underlying_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (𝒜 : TopCat.Presheaf C X) :
    IsSheafOfAlgebraicStructures (F := F) 𝒜 ↔
      TopCat.Presheaf.IsSheaf (underlyingPresheaf F 𝒜) := by
  exact categoryValuedSheaf_iff_underlying_isSheaf F 𝒜

/-- The underlying presheaf of the pointwise product is a sheaf of sets,
matching the pointwise-product example from the preceding sheaf section. -/
theorem pointwiseProductPresheaf_underlying_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) :
    TopCat.Presheaf.IsSheaf
      (underlyingPresheaf F (pointwiseProductPresheaf (F := F) A)) := by
  sorry

/-- The pointwise product presheaf is a sheaf of algebraic structures. -/
theorem pointwiseProductPresheaf_isSheaf
    {C : Type u} [Category.{v} C] {F : C ⥤ Type v}
    [AlgebraicStructureType C F] {X : TopCat.{v}}
    (A : X → C) :
    IsSheafOfAlgebraicStructures (F := F)
      (pointwiseProductPresheaf (F := F) A) := by
  exact (isSheafOfAlgebraicStructures_iff_underlying_isSheaf
    (F := F) (pointwiseProductPresheaf (F := F) A)).2
    (pointwiseProductPresheaf_underlying_isSheaf (F := F) A)

end

end Formalization.Books.Sheaves.Unit15
