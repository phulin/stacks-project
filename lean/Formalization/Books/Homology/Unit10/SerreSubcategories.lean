import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Homological Algebra, Chapter 10: Serre subcategories

Mathlib's `ObjectProperty.IsSerreClass` is the canonical interface for the
source's Serre subcategories.  A property `P` presents the corresponding full
subcategory as `P.FullSubcategory`; its closure-under-isomorphisms instance is
the source's strictly-full condition.  The quotient construction is likewise
the canonical localization at `P.isoModSerre`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

universe v u v' u'

namespace CategoryTheory
namespace ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The exact-five-term closure condition used for weak Serre subcategories.

The parent `Nonempty` field records the source's nonemptiness requirement;
`P.FullSubcategory` supplies the corresponding full subcategory. -/
class IsWeakSerreClass (P : ObjectProperty C) : Prop extends P.Nonempty where
  prop_X₂_of_exact {S : ComposableArrows C 4} (hS : S.Exact)
      (h₀ : P (S.obj' 0)) (h₁ : P (S.obj' 1))
      (h₃ : P (S.obj' 3)) (h₄ : P (S.obj' 4)) : P (S.obj' 2)

lemma prop_X₂_of_exact_weakSerre {P : ObjectProperty C} [P.IsWeakSerreClass]
    {S : ComposableArrows C 4} (hS : S.Exact)
    (h₀ : P (S.obj' 0)) (h₁ : P (S.obj' 1))
    (h₃ : P (S.obj' 3)) (h₄ : P (S.obj' 4)) : P (S.obj' 2) :=
  IsWeakSerreClass.prop_X₂_of_exact hS h₀ h₁ h₃ h₄

end ObjectProperty
end CategoryTheory

namespace Formalization.Books.Homology.Unit10

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ## Serre and weak Serre subcategories -/

/- `ObjectProperty.IsSerreClass` is Mathlib's source-faithful definition of a
Serre subcategory.  Its `FullSubcategory` is full, and closure under
isomorphisms is the strict-full condition. -/

theorem serre_subcategory_is_nonempty_and_full
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty P.FullSubcategory ∧ Nonempty P.ι.FullyFaithful := by
  exact ⟨inferInstance, ⟨P.fullyFaithfulι⟩⟩

theorem serre_subcategory_characterization
    (P : ObjectProperty C) :
    P.IsSerreClass ↔
      P (0 : C) ∧
        P.IsClosedUnderIsomorphisms ∧
          (P.IsClosedUnderSubobjects ∧ P.IsClosedUnderQuotients) ∧
            P.IsClosedUnderExtensions := by
  sorry

theorem serre_subcategory_is_abelian_and_inclusion_exact
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty (Abelian P.FullSubcategory) ∧
      exactFunctor P.FullSubcategory C P.ι := by
  sorry

/- The class above is the source's nonempty full subcategory closed under
exact five-term sequences. -/

theorem weak_serre_subcategory_definition
    (P : ObjectProperty C) :
    P.IsWeakSerreClass ↔
      Nonempty P.FullSubcategory ∧
        ∀ (S : ComposableArrows C 4), S.Exact →
          P (S.obj' 0) → P (S.obj' 1) → P (S.obj' 3) → P (S.obj' 4) →
            P (S.obj' 2) := by
  sorry

theorem weak_serre_subcategory_is_nonempty_and_full
    (P : ObjectProperty C) [P.IsWeakSerreClass] :
    Nonempty P.FullSubcategory ∧ Nonempty P.ι.FullyFaithful := by
  exact ⟨inferInstance, ⟨P.fullyFaithfulι⟩⟩

theorem weak_serre_subcategory_characterization
    (P : ObjectProperty C) :
    P.IsWeakSerreClass ↔
      P (0 : C) ∧
        P.IsClosedUnderIsomorphisms ∧
          (P.IsClosedUnderKernels ∧ P.IsClosedUnderCokernels) ∧
            P.IsClosedUnderExtensions := by
  sorry

theorem weak_serre_subcategory_is_abelian_and_inclusion_exact
    (P : ObjectProperty C) [P.IsWeakSerreClass] :
    Nonempty (Abelian P.FullSubcategory) ∧
      exactFunctor P.FullSubcategory C P.ι := by
  sorry

/-! ## Kernels of exact functors -/

theorem exact_functor_kernel_is_serre_subcategory
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ₑ D) :
    (Functor.kernel F.obj).IsSerreClass := by
  infer_instance

/- The source's `Ker(F)` is the full subcategory associated to Mathlib's
canonical object property `Functor.kernel F`. -/
abbrev kernelCategory
    {D : Type u'} [Category.{v'} D]
    [Abelian D] (F : C ⥤ₑ D) : Type u :=
  (Functor.kernel F.obj).FullSubcategory

/-! ## The Serre quotient -/

abbrev serreQuotient (P : ObjectProperty C) [P.IsSerreClass] :=
  P.isoModSerre.Localization

noncomputable abbrev serreQuotientFunctor
    (P : ObjectProperty C) [P.IsSerreClass] :
    C ⥤ serreQuotient P :=
  P.isoModSerre.Q

@[instance_reducible]
noncomputable def serreQuotientAbelian
    (P : ObjectProperty C) [P.IsSerreClass] :
    Abelian (serreQuotient P) :=
  ObjectProperty.SerreClassLocalization.abelian
    (serreQuotientFunctor P) P

noncomputable def serreQuotientExactFunctor
    (P : ObjectProperty C) [P.IsSerreClass] :
    C ⥤ₑ serreQuotient P := by
  letI : PreservesFiniteLimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteLimits
      (serreQuotientFunctor P) P
  letI : PreservesFiniteColimits (serreQuotientFunctor P) :=
    ObjectProperty.SerreClassLocalization.preservesFiniteColimits
      (serreQuotientFunctor P) P
  exact ExactFunctor.of (serreQuotientFunctor P)

theorem serre_quotient_is_abelian_exact_essentially_surjective
    (P : ObjectProperty C) [P.IsSerreClass] :
    Nonempty (Abelian (serreQuotient P)) ∧
      exactFunctor C (serreQuotient P) (serreQuotientFunctor P) ∧
        (serreQuotientFunctor P).EssSurj ∧
          Functor.kernel (serreQuotientFunctor P) = P := by
  refine ⟨⟨serreQuotientAbelian P⟩, (serreQuotientExactFunctor P).property, ?_, ?_⟩
  · exact Localization.essSurj (serreQuotientFunctor P) P.isoModSerre
  · ext X
    exact ObjectProperty.SerreClassLocalization.isZero_obj_iff
      (serreQuotientFunctor P) P X

/- The source's universal property is stated using exact functors as objects
of Mathlib's bundled `ExactFunctor` category. -/
theorem serre_quotient_universal_property
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    ∃! H : serreQuotient P ⥤ₑ D,
      serreQuotientFunctor P ⋙ H.obj = G.obj := by
  sorry

noncomputable def inducedSerreQuotientFunctor
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    serreQuotient P ⥤ₑ D :=
  (serre_quotient_universal_property P G hG).choose

theorem inducedSerreQuotientFunctor_fac
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    serreQuotientFunctor P ⋙ (inducedSerreQuotientFunctor P G hG).obj = G.obj :=
  (serre_quotient_universal_property P G hG).choose_spec.1

/-! ## Faithfulness of the induced functor -/

theorem quotient_by_kernel_exact_functor_iff_faithful
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (P : ObjectProperty C) [P.IsSerreClass]
    (G : C ⥤ₑ D) (hG : P ≤ Functor.kernel G.obj) :
    P = Functor.kernel G.obj ↔
      (inducedSerreQuotientFunctor P G hG).obj.Faithful := by
  sorry

end Formalization.Books.Homology.Unit10
