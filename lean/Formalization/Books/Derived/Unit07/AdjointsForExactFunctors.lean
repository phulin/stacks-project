import Formalization.Books.Derived.Unit03.Definitions
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Derived Categories, Chapter 7: adjoints for exact functors

This file records the two results in the source section.  Exact functors,
adjunctions, fully faithful functors, zero objects, and kernels are expressed
with Mathlib's canonical interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Homology.Unit03

namespace Formalization.Books.Derived.Unit07

section TriangulatedCategories

variable {C D : Type*} [Category* C] [Category* D]
  [AdditiveCategory C] [AdditiveCategory D]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

/-!
The source's displayed Yoneda bijection and triangle comparison are the proof
mechanism for the following statement.  Mathlib packages the same mechanism
as `Adjunction.isTriangulated_rightAdjoint`; its right-adjoint shift structure
is constructed canonically from the shift structure on the left adjoint.
-/

/-- A right adjoint of an exact functor between triangulated categories is exact. -/
theorem right_adjoint_of_exact_is_exact
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.CommShift ℤ] [F.IsTriangulated]
    [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D] :
    letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    G.IsTriangulated := by
  exact
    letI : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
    letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
    adj.isTriangulated_rightAdjoint

/-!
For the second source lemma, `Functor.kernel G` is the canonical object
property `X ↦ IsZero (G.obj X)`.  Thus “the kernel of `G` is zero” is recorded
as the source-faithful reflection-of-zero hypothesis below.
-/

/-- A fully faithful exact functor with an exact right adjoint of zero kernel
is an equivalence of categories. -/
theorem fully_faithful_adjoint_kernel_zero_is_equivalence
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    [F.CommShift ℤ] [F.IsTriangulated]
    [G.CommShift ℤ] [G.IsTriangulated]
    [CategoryTheory.IsTriangulated C] [CategoryTheory.IsTriangulated D]
    (hF : Nonempty F.FullyFaithful)
    (hG : ∀ X : D, Functor.kernel G X → IsZero X) :
    F.IsEquivalence := by
  have hFull : F.Full := hF.some.full
  have hFaithful : F.Faithful := hF.some.faithful
  have hUnit : IsIso adj.unit :=
    @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ _ _ adj hFull hFaithful
  have hUnitApp : ∀ X, IsIso (adj.unit.app X) := by
    rw [← NatTrans.isIso_iff_isIso_app]
    exact hUnit
  have hCounit : ∀ Y, IsIso (adj.counit.app Y) := by
    intro Y
    obtain ⟨Z, f, g, hT⟩ := distinguished_cocone_triangle (adj.counit.app Y)
    have hT' := G.map_distinguished (Triangle.mk (adj.counit.app Y) f g) hT
    have hi : IsIso (G.map (adj.counit.app Y)) :=
      @isIso_of_hom_comp_eq_id _ _ _ _
        (adj.unit.app (G.obj Y)) (hUnitApp _) (G.map (adj.counit.app Y))
        (adj.right_triangle_components Y)
    exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
      (hG Z ((Triangle.isZero₃_iff_isIso₁ _ hT').2 hi))
  refine { faithful := hFaithful, full := hFull, essSurj := ?_ }
  refine { mem_essImage := ?_ }
  intro Y
  refine ⟨G.obj Y, ⟨?_⟩⟩
  exact @asIso _ _ _ _ (adj.counit.app Y) (hCounit Y)

end TriangulatedCategories

end Formalization.Books.Derived.Unit07
