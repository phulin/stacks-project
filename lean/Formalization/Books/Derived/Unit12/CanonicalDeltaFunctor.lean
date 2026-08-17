import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.Subcategory
import Formalization.Books.Derived.Unit11.DerivedCategories

/-!
# Derived Categories, Chapter 12: the canonical delta-functor

The canonical connecting morphism in the derived category is Mathlib's
DerivedCategory.triangleOfSESδ. This file records the source construction
and its bounded, truncation, comparison, and vanishing-composition interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit12

/-! ## The obstruction in the homotopy category -/

/-- A short exact sequence which is not split. -/
def HasNonsplitShortExactSequence
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∃ S : ShortComplex C, S.ShortExact ∧ ¬ Nonempty S.Splitting

/-- The homotopy-category functor on cochain complexes. -/
noncomputable abbrev homotopyCanonicalFunctor
    (C : Type u) [Category.{v} C] [Abelian C] :
    CochainComplex C ℤ ⥤ HomotopyCategory C (.up ℤ) :=
  HomotopyCategory.quotient C (.up ℤ)

/-- The single-complex calculation used in the nonsplit-extension warning. -/
theorem homotopy_single_shift_hom_eq_zero
    (C : Type u) [Category.{v} C] [Abelian C] (A B : C) :
    ∀ f : (HomotopyCategory.singleFunctor C 0).obj B ⟶
      (shiftFunctor (HomotopyCategory C (.up ℤ)) (1 : ℤ)).obj
        ((HomotopyCategory.singleFunctor C 0).obj A),
      f = 0 := by
  sorry

/-- A delta-functor structure on the homotopy-category functor would split every
short exact sequence of objects. -/
theorem homotopy_delta_functor_forces_splitting
    {C : Type u} [Category.{v} C] [Abelian C]
    (G : DeltaFunctor (homotopyCanonicalFunctor C))
    {S : ShortComplex C} (hS : S.ShortExact) :
    Nonempty S.Splitting := by
  sorry

/-- Hence the homotopy-category functor is not a delta-functor whenever a
nonsplit short exact sequence exists. -/
theorem homotopyCanonicalFunctor_not_deltaFunctor_of_nonsplit
    (C : Type u) [Category.{v} C] [Abelian C]
    (hC : HasNonsplitShortExactSequence C) :
    ¬ Nonempty (DeltaFunctor (homotopyCanonicalFunctor C)) := by
  sorry

/-! ## The mapping-cone construction -/

/-- The mapping-cone projection associated with a short complex. -/
noncomputable def coneToShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (CochainComplex C ℤ)) :
    CochainComplex.mappingCone S.f ⟶ S.X₃ :=
  CochainComplex.mappingCone.descShortComplex S

/-- The mapping-cone component is the standard biproduct of the shifted source
and the target. -/
noncomputable def mappingConeComponentIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (n : ℤ) :
    (CochainComplex.mappingCone S.f).X n ≅
      S.X₁.X (n + 1) ⊞ S.X₂.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod S.f n (n + 1) rfl

@[reassoc (attr := simp)]
theorem coneToShortExact_comp_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} :
    CochainComplex.mappingCone.inr S.f ≫ coneToShortExact S = S.g :=
  CochainComplex.mappingCone.inr_descShortComplex S

/-- The mapping-cone projection is a quasi-isomorphism for a short exact
sequence of complexes. -/
theorem coneToShortExact_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    QuasiIso (coneToShortExact S) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex hS

theorem coneToShortExact_derived_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    IsIso (DerivedCategory.Q.map (coneToShortExact S)) := by
  sorry

/-- The kernel of q is the cone of the identity on the first complex. -/
theorem coneToShortExact_kernel_iso_mappingCone_identity
    {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    Nonempty
      (kernel (coneToShortExact S) ≅
        CochainComplex.mappingCone (𝟙 S.X₁)) := by
  sorry

/-- The kernel of the mapping-cone projection is represented by the acyclic
cone of the identity. -/
theorem mappingCone_identity_acyclic
    (C : Type u) [Category.{v} C] [Abelian C]
    (A : CochainComplex C ℤ) :
    (CochainComplex.mappingCone (𝟙 A)).Acyclic := by
  sorry

/-- The mapping-cone triangle is distinguished already in the homotopy
category, before applying the derived localization. -/
theorem mappingConeTriangleh_distinguished
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    CochainComplex.mappingCone.triangleh f ∈
      distTriang (HomotopyCategory C (.up ℤ)) :=
  coneTriangleh_distinguished f

/-! ## The canonical connecting morphism and delta-functor -/

/-- The source connecting morphism, expressed using the canonical cone triangle
and the localization commutation isomorphism. -/
noncomputable def canonicalDerivedDelta
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    (DerivedCategory.Q (C := C)).obj S.X₃ ⟶
      ((DerivedCategory.Q (C := C)).obj S.X₁)⟦(1 : ℤ)⟧ :=
  letI : QuasiIso (coneToShortExact S) := coneToShortExact_quasiIso hS
  inv (DerivedCategory.Q.map (coneToShortExact S)) ≫
    DerivedCategory.Q.map ((CochainComplex.mappingCone.triangle S.f).mor₃) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁

/-- The cone formula is Mathlib's canonical connecting morphism. -/
theorem canonicalDerivedDelta_eq_triangleOfSESδ
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedDelta hS = DerivedCategory.triangleOfSESδ hS := by
  sorry

/-- The distinguished triangle attached to a short exact sequence of complexes. -/
noncomputable def canonicalDerivedTriangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    Triangle (DerivedCategory C) :=
  Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g)
    (canonicalDerivedDelta hS)

theorem canonicalDerivedTriangle_distinguished
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedTriangle hS ∈ distTriang (DerivedCategory C) := by
  sorry

/-- The canonical triangle is the cone triangle after localization. -/
noncomputable def canonicalDerivedTriangleIsoCone
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    canonicalDerivedTriangle hS ≅
      (DerivedCategory.Q (C := C)).mapTriangle.obj
        (CochainComplex.mappingCone.triangle S.f) :=
  let e : canonicalDerivedTriangle hS = DerivedCategory.triangleOfSES hS := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ hS]
  eqToIso e ≪≫ DerivedCategory.triangleOfSESIso hS

/-- Naturality of the connecting morphism for a morphism of short exact
sequences. -/
theorem canonicalDerivedDelta_naturality
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    canonicalDerivedDelta h₁ ≫
        (DerivedCategory.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map φ.τ₃ ≫ canonicalDerivedDelta h₂ := by
  sorry

/-- The cone map induced by a morphism of short exact sequences. -/
noncomputable def mappingConeMapOfShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    CochainComplex.mappingCone S₁.f ⟶ CochainComplex.mappingCone S₂.f :=
  CochainComplex.mappingCone.map S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

theorem mappingConeMapOfShortComplex_desc_naturality
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    mappingConeMapOfShortComplex φ ≫ coneToShortExact S₂ =
      coneToShortExact S₁ ≫ φ.τ₃ :=
  by
    simpa [mappingConeMapOfShortComplex, coneToShortExact] using
      (CochainComplex.mappingCone.descShortComplex_naturality φ)

/-- The cone triangle map satisfies the third commutative square used in the
naturality proof. -/
noncomputable def mappingConeTriangleMapOfShortComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    CochainComplex.mappingCone.triangle S₁.f ⟶
      CochainComplex.mappingCone.triangle S₂.f :=
  CochainComplex.mappingCone.triangleMap S₁.f S₂.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm

theorem mappingConeTriangleMapOfShortComplex_comm₃
    {C : Type u} [Category.{v} C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂) :
    (mappingConeTriangleMapOfShortComplex φ).hom₃ ≫
        (CochainComplex.mappingCone.triangle S₂.f).mor₃ =
      (CochainComplex.mappingCone.triangle S₁.f).mor₃ ≫
        (φ.τ₁)⟦(1 : ℤ)⟧' :=
  (mappingConeTriangleMapOfShortComplex φ).comm₃.symm

/-- The canonical delta-functor on all cochain complexes. -/
noncomputable def canonicalDerivedDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (DerivedCategory.Q (C := C)) where
  delta := fun S hS => canonicalDerivedDelta hS
  distinguished := fun S hS => canonicalDerivedTriangle_distinguished hS
  naturality := by
    intro S₁ S₂ φ h₁ h₂
    exact (canonicalDerivedDelta_naturality h₁ h₂ φ).symm

/-! ## Bounded variants -/

/- The existing DeltaFunctor structure is parameterized by an abelian source
category.  The bounded full subcategories are abelian because boundedness is
stable under the finite limits and colimits used for kernels and cokernels.
These three closure interfaces are the only missing subcategory instances in
the imported API. -/

theorem cochainPlus_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (CochainComplex.plus C).ContainsZero := by
  sorry

theorem cochainPlus_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (CochainComplex.plus C) := by
  sorry

theorem cochainPlus_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus C) := by
  sorry

theorem cochainPlus_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (CochainComplex.plus C) := by
  sorry

theorem boundedAbove_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedAboveProperty C).ContainsZero := by
  sorry

theorem boundedAbove_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (boundedAboveProperty C) := by
  sorry

theorem boundedAbove_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (boundedAboveProperty C) := by
  sorry

theorem boundedAbove_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (boundedAboveProperty C) := by
  sorry

theorem bounded_containsZero
    (C : Type u) [Category.{v} C] [Abelian C] :
    (boundedProperty C).ContainsZero := by
  sorry

theorem bounded_isClosedUnderKernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderKernels (boundedProperty C) := by
  sorry

theorem bounded_isClosedUnderCokernels
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderCokernels (boundedProperty C) := by
  sorry

theorem bounded_isClosedUnderFiniteProducts
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty.IsClosedUnderFiniteProducts (boundedProperty C) := by
  sorry

noncomputable instance compPlus_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompPlus C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (CochainComplex.plus C).ContainsZero := cochainPlus_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (CochainComplex.plus C) :=
    cochainPlus_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance compMinus_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompMinus C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (boundedAboveProperty C).ContainsZero := boundedAbove_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (boundedAboveProperty C) :=
    boundedAbove_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance compBounded_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (CompBounded C) := by
  letI : Abelian (CochainComplex C ℤ) :=
    Formalization.Books.Homology.Unit13.cochainComplex_abelian C
  letI : (boundedProperty C).ContainsZero := bounded_containsZero C
  letI : ObjectProperty.IsClosedUnderKernels (boundedProperty C) :=
    bounded_isClosedUnderKernels C
  letI : ObjectProperty.IsClosedUnderCokernels (boundedProperty C) :=
    bounded_isClosedUnderCokernels C
  letI : ObjectProperty.IsClosedUnderFiniteProducts (boundedProperty C) :=
    bounded_isClosedUnderFiniteProducts C
  infer_instance

noncomputable instance derivedPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DPlus C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

noncomputable instance derivedMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DMinus C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

noncomputable instance derivedBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DBounded C) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

/-- The bounded-below complex-to-derived functor supplied by Mathlib. -/
noncomputable abbrev canonicalPlusFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompPlus C ⥤ DPlus C :=
  DerivedCategory.Plus.Q (C := C)

/-- The image of a bounded-above complex lies in the bounded-above derived
subcategory. -/
theorem canonicalMinusFunctor_obj_mem
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : CompMinus C) :
    derivedMinusProperty C
      (((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) := by
  sorry

/-- The bounded-above complex-to-derived functor, obtained by the canonical
full-subcategory lift. -/
noncomputable def canonicalMinusFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompMinus C ⥤ DMinus C :=
  (derivedMinusProperty C).lift
    ((boundedAboveProperty C).ι ⋙ DerivedCategory.Q (C := C))
    (canonicalMinusFunctor_obj_mem C)

/-- The image of a bounded complex lies in the bounded derived subcategory. -/
theorem canonicalBoundedFunctor_obj_mem
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : CompBounded C) :
    derivedBoundedProperty C
      (((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C)).obj X) := by
  sorry

/-- The bounded complex-to-derived functor, obtained by the canonical
full-subcategory lift. -/
noncomputable def canonicalBoundedFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CompBounded C ⥤ DBounded C :=
  (derivedBoundedProperty C).lift
    ((boundedProperty C).ι ⋙ DerivedCategory.Q (C := C))
    (canonicalBoundedFunctor_obj_mem C)

/-- The canonical delta-functor structure on the bounded-below functor. -/
theorem canonicalPlusFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalPlusFunctor C)) := by
  sorry

/-- The canonical delta-functor structure on the bounded-above functor. -/
theorem canonicalMinusFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalMinusFunctor C)) := by
  sorry

/-- The canonical delta-functor structure on the bounded functor. -/
theorem canonicalBoundedFunctor_isDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Nonempty (DeltaFunctor (canonicalBoundedFunctor C)) := by
  sorry

noncomputable def canonicalPlusDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalPlusFunctor C) :=
  Classical.choice (canonicalPlusFunctor_isDeltaFunctor C)

noncomputable def canonicalMinusDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalMinusFunctor C) :=
  Classical.choice (canonicalMinusFunctor_isDeltaFunctor C)

noncomputable def canonicalBoundedDeltaFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    DeltaFunctor (canonicalBoundedFunctor C) :=
  Classical.choice (canonicalBoundedFunctor_isDeltaFunctor C)

/-! ## Comparison triangles -/

/-- The morphism of canonical derived triangles induced by a morphism of short
exact sequences. -/
noncomputable def canonicalDerivedTriangleMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    canonicalDerivedTriangle h₁ ⟶ canonicalDerivedTriangle h₂ :=
  let e₁ : canonicalDerivedTriangle h₁ = DerivedCategory.triangleOfSES h₁ := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ h₁]
  let e₂ : canonicalDerivedTriangle h₂ = DerivedCategory.triangleOfSES h₂ := by
    dsimp [canonicalDerivedTriangle, DerivedCategory.triangleOfSES]
    rw [canonicalDerivedDelta_eq_triangleOfSESδ h₂]
  eqToHom e₁ ≫ DerivedCategory.triangleOfSES.map h₁ h₂ φ ≫ eqToHom e₂.symm

/-- If all three vertical maps of short exact sequences are quasi-isomorphisms,
then the induced triangle map is an isomorphism. -/
theorem canonicalDerivedTriangleMap_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (hφ₁ : QuasiIso φ.τ₁) (hφ₂ : QuasiIso φ.τ₂) (hφ₃ : QuasiIso φ.τ₃) :
    IsIso (canonicalDerivedTriangleMap h₁ h₂ φ) := by
  sorry

noncomputable def canonicalDerivedTriangleMapIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂)
    (hφ₁ : QuasiIso φ.τ₁) (hφ₂ : QuasiIso φ.τ₂) (hφ₃ : QuasiIso φ.τ₃) :
    canonicalDerivedTriangle h₁ ≅ canonicalDerivedTriangle h₂ := by
  letI : IsIso (canonicalDerivedTriangleMap h₁ h₂ φ) :=
    canonicalDerivedTriangleMap_isIso h₁ h₂ φ hφ₁ hφ₂ hφ₃
  exact asIso (canonicalDerivedTriangleMap h₁ h₂ φ)

/-- The cone triangle and the canonical triangle agree for a termwise split
short exact sequence, after passage to the derived category. -/
theorem canonicalDerivedTriangle_termwiseSplit_comparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B D : Formalization.Books.Derived.Unit09.BookComplex C}
    (S : TermwiseSplitExactSequence A B D) :
    Nonempty
      (canonicalDerivedTriangle
          (termwiseSplitShortComplex_shortExact C S) ≅
        (DerivedCategory.Q (C := C)).mapTriangle.obj
          (termwiseSplitTriangle S)) := by
  sorry

/-- The same comparison stated with the termwise-split triangle in the
homotopy category, followed by the derived localization. -/
theorem canonicalDerivedTriangle_termwiseSplit_K_comparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B D : Formalization.Books.Derived.Unit09.BookComplex C}
    (S : TermwiseSplitExactSequence A B D) :
    Nonempty
      (canonicalDerivedTriangle
          (termwiseSplitShortComplex_shortExact C S) ≅
        (DerivedCategory.Qh (C := C)).mapTriangle.obj
          (termwiseSplitTriangleh S)) := by
  sorry

/-! ## Truncation triangles -/

/-- The canonical t-structure used for all truncation statements. -/
abbrev canonicalTStructure
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    CategoryTheory.Triangulated.TStructure (DerivedCategory C) :=
  DerivedCategory.TStructure.t

/-- The source cohomology piece H^n(K)[-n], using the derived single functor
and the canonical derived homology functor. -/
noncomputable def canonicalCohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C n).obj
    ((DerivedCategory.homologyFunctor C n).obj
      ((DerivedCategory.Q (C := C)).obj K))

/-- The truncation triangle built from the short exact truncation sequence and
the quotient-to-upper-truncation quasi-isomorphism. -/
noncomputable def canonicalTruncationTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  let h := K.shortComplexTruncLE_shortExact a
  let e := K.shortComplexTruncLEX₃ToTruncGE a (a + 1) (by lia)
  Triangle.mk
    (DerivedCategory.Q.map (K.ιTruncLE a))
    (DerivedCategory.Q.map (K.πTruncGE (a + 1)))
    (inv (DerivedCategory.Q.map e) ≫
      (DerivedCategory.triangleOfSES h).mor₃)

theorem canonicalTruncationTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    canonicalTruncationTriangle C K a ∈ distTriang (DerivedCategory C) := by
  sorry

/-- The direct short-exact construction agrees with the canonical t-structure
truncation triangle. -/
theorem canonicalTruncationTriangle_isomorphic_to_tStructure
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      (canonicalTruncationTriangle C K a ≅
        ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

/-- The quotient-to-upper-truncation map used in the canonical truncation
triangle is a quasi-isomorphism. -/
instance canonicalTruncation_quotient_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C]
    (_K : CochainComplex C ℤ) (_a : ℤ) :
    QuasiIso (_K.shortComplexTruncLEX₃ToTruncGE _a (_a + 1) (by lia)) := by
  infer_instance

/-- The lower truncation step triangle, whose third object is the cohomology
piece in degree a + 1. -/
noncomputable def lowerTruncationStepTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
    (((canonicalTStructure C).truncLE (a + 1)).obj
      ((DerivedCategory.Q (C := C)).obj K))

theorem lowerTruncationStepTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    lowerTruncationStepTriangle C K a ∈ distTriang (DerivedCategory C) :=
  (canonicalTStructure C).triangleLEGE_distinguished a (a + 1) rfl _

theorem lowerTruncationStepTriangle_third_is_cohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₃ ≅
        canonicalCohomologyPiece C K (a + 1)) := by
  sorry

theorem lowerTruncationStepTriangle_first_is_lowerTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₁ ≅
        ((canonicalTStructure C).truncLE a).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

theorem lowerTruncationStepTriangle_second_is_nextLowerTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((lowerTruncationStepTriangle C K a).obj₂ ≅
        ((canonicalTStructure C).truncLE (a + 1)).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

/-- The upper truncation step triangle, whose first object is the cohomology
piece in degree a. -/
noncomputable def upperTruncationStepTriangle
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) : Triangle (DerivedCategory C) :=
  ((canonicalTStructure C).triangleLEGE a (a + 1) rfl).obj
    (((canonicalTStructure C).truncGE a).obj
      ((DerivedCategory.Q (C := C)).obj K))

theorem upperTruncationStepTriangle_distinguished
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    upperTruncationStepTriangle C K a ∈ distTriang (DerivedCategory C) :=
  (canonicalTStructure C).triangleLEGE_distinguished a (a + 1) rfl _

theorem upperTruncationStepTriangle_first_is_cohomologyPiece
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₁ ≅
        canonicalCohomologyPiece C K a) := by
  sorry

theorem upperTruncationStepTriangle_second_is_upperTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₂ ≅
        ((canonicalTStructure C).truncGE a).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

theorem upperTruncationStepTriangle_third_is_nextUpperTruncation
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (a : ℤ) :
    Nonempty
      ((upperTruncationStepTriangle C K a).obj₃ ≅
        ((canonicalTStructure C).truncGE (a + 1)).obj
          ((DerivedCategory.Q (C := C)).obj K)) := by
  sorry

/-! ## Vanishing compositions and truncation factorization -/

/-- The map of the reverse-indexed adjacent arrow K_{j+1} to K_j in a chain
written from K_n on the left to K_0 on the right. -/
def reverseAdjacentMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n) (j : Fin n) :
    F.obj ⟨n - j.val - 1, by omega⟩ ⟶
      F.obj ⟨n - j.val, by omega⟩ :=
  F.map (homOfLE (by simp only [Fin.mk_le_mk]; omega))

/-- If H^i(K_0)=0 for i>0 and the maps on H^{-j} vanish, the composite
K_0 to K_n factors through tau<=-n K_n in the derived category. -/
theorem vanishingComposition_factorization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n)
    (h₀ : ∀ i : ℤ, 0 < i → IsZero (F.left.homology i))
    (h₁ : ∀ j : Fin n,
      HomologicalComplex.homologyMap (adjacentMap F j) (-(j.val : ℤ)) = 0) :
    ∃ u : (DerivedCategory.Q (C := C)).obj F.left ⟶
        (DerivedCategory.Q (C := C)).obj (F.right.truncLE (-(n : ℤ))),
      u ≫ DerivedCategory.Q.map (F.right.ιTruncLE (-(n : ℤ))) =
        DerivedCategory.Q.map F.hom := by
  sorry

/-- Dually, for a reverse-indexed chain with H^i(K_0)=0 for i<0 and
vanishing maps on H^j, the composite factors through tau>=n K_n. -/
theorem vanishingComposition_factorization_dual
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {n : ℕ} (F : ComposableArrows (CochainComplex C ℤ) n)
    (h₀ : ∀ i : ℤ, i < 0 → IsZero (F.right.homology i))
    (h₁ : ∀ j : Fin n,
      HomologicalComplex.homologyMap (reverseAdjacentMap F j) (j.val : ℤ) = 0) :
    ∃ u : (DerivedCategory.Q (C := C)).obj (F.left.truncGE (n : ℤ)) ⟶
        (DerivedCategory.Q (C := C)).obj F.right,
      DerivedCategory.Q.map (F.left.πTruncGE (n : ℤ)) ≫ u =
        DerivedCategory.Q.map F.hom := by
  sorry

end Formalization.Books.Derived.Unit12
