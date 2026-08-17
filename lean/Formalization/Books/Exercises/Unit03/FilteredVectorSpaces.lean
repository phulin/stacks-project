import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.LinearAlgebra.Prod

/-!
# Exercises, Chapter 3: filtered vector spaces

This file records the three assertions in the filtered-vector-space exercise.
The filtered-vector-space category and its universal-property infrastructure
are reused from Homology, Chapter 3.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Exercises.Unit03

/-! ## (1) Additivity and direct sums -/

/-- The direct sum of filtered vector spaces has the product underlying module
and the product filtration at every index. -/
def filteredVectorSpaceDirectSum
    {k : Type u} [Field k]
    (V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :
    Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (V.underlying × W.underlying)
  filtration := fun i => Submodule.prod (V.filtration i) (W.filtration i)
  decreasing := by
    intro i
    exact Submodule.prod_mono (V.decreasing i) (W.decreasing i)

theorem filteredVectorSpaceDirectSum_mem_iff
    {k : Type u} [Field k]
    (V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k)
    (i : ℤ) (x : V.underlying × W.underlying) :
    x ∈ (filteredVectorSpaceDirectSum V W).filtration i ↔
      x.1 ∈ V.filtration i ∧ x.2 ∈ W.filtration i := by
  rfl

/-- Filtered vector spaces form an additive category. -/
theorem filteredVectorSpace_additive
    (k : Type u) [Field k] :
    Nonempty
      (Formalization.Books.Homology.Unit03.AdditiveCategory
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k)) := by
  sorry

/-! ## (2) Induced kernels and quotient cokernels -/

/-- The induced filtration on the ordinary module kernel of a filtered map. -/
def filteredVectorSpaceKernelObject
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (LinearMap.ker f.1.hom)
  filtration := fun i =>
    (V.filtration i).comap (LinearMap.ker f.1.hom).subtype
  decreasing := by
    intro i
    exact Submodule.comap_mono (V.decreasing i)

/-- The filtered inclusion of the induced kernel. -/
def filteredVectorSpaceKernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : filteredVectorSpaceKernelObject f ⟶ V :=
  ⟨ModuleCat.ofHom (LinearMap.ker f.1.hom).subtype, by
    intro i x hx
    exact hx⟩

theorem filteredVectorSpaceKernelMap_comp
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : filteredVectorSpaceKernelMap f ≫ f = 0 := by
  sorry

def filteredVectorSpaceKernelFork
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : KernelFork f :=
  KernelFork.ofι (filteredVectorSpaceKernelMap f)
    (filteredVectorSpaceKernelMap_comp f)

/-- The induced-filtration kernel fork is universal. -/
theorem filteredVectorSpaceKernelFork_isLimit
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Nonempty (IsLimit (filteredVectorSpaceKernelFork f)) := by
  sorry

/-- The quotient module of a filtered map with its quotient filtration. -/
def filteredVectorSpaceCokernelObject
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : Formalization.Books.Homology.Unit03.FilteredVectorSpace k where
  underlying := ModuleCat.of k (W.underlying ⧸ LinearMap.range f.1.hom)
  filtration := fun i =>
    Submodule.map (LinearMap.range f.1.hom).mkQ (W.filtration i)
  decreasing := by
    intro i
    exact Submodule.map_mono (W.decreasing i)

/-- The filtered quotient map for the quotient filtration. -/
def filteredVectorSpaceCokernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : W ⟶ filteredVectorSpaceCokernelObject f :=
  ⟨ModuleCat.ofHom (LinearMap.range f.1.hom).mkQ, by
    intro i x hx
    exact ⟨x, hx, rfl⟩⟩

theorem filteredVectorSpace_comp_cokernelMap
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : f ≫ filteredVectorSpaceCokernelMap f = 0 := by
  sorry

def filteredVectorSpaceCokernelCofork
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) : CokernelCofork f :=
  CokernelCofork.ofπ (filteredVectorSpaceCokernelMap f)
    (filteredVectorSpace_comp_cokernelMap f)

/-- The quotient-filtration cokernel cofork is universal. -/
theorem filteredVectorSpaceCokernelCofork_isColimit
    {k : Type u} [Field k]
    {V W : Formalization.Books.Homology.Unit03.FilteredVectorSpace k}
    (f : V ⟶ W) :
    Nonempty (IsColimit (filteredVectorSpaceCokernelCofork f)) := by
  sorry

/-! ## (3) The coimage/image counterexample -/

/-- The source's filtered-vector-space example has zero kernel and cokernel,
but its identity-on-underlying-spaces map is not an isomorphism. -/
theorem filteredVectorSpace_counterexample
    (k : Type u) [Field k] :
    letI : HasKernels
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
      Formalization.Books.Homology.Unit03.filtered_vector_space_has_kernels k
    letI : HasCokernels
        (Formalization.Books.Homology.Unit03.FilteredVectorSpace k) :=
      Formalization.Books.Homology.Unit03.filtered_vector_space_has_cokernels k
    IsZero
        (kernel
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) ∧
      IsZero
        (cokernel
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) ∧
      ¬ IsIso
        (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ∧
      Nonempty
        (Abelian.coimage
            (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ≅
          Formalization.Books.Homology.Unit03.filteredLineV k) ∧
      Nonempty
        (Abelian.image
            (Formalization.Books.Homology.Unit03.filteredLineIdentity k) ≅
          Formalization.Books.Homology.Unit03.filteredLineW k) ∧
      ¬ IsIso
        (Abelian.coimageImageComparison
          (Formalization.Books.Homology.Unit03.filteredLineIdentity k)) := by
  sorry

end Formalization.Books.Exercises.Unit03
