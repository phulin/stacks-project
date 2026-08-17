import Formalization.Books.Homology.Unit04.KaroubianCategories
import Formalization.Books.Categories.Unit43.MonoidalCategories
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.GradedObject.Braiding
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.DirectSum.Finite

/-!
# Homological Algebra, Chapter 17: Additive monoidal categories

This file records the source definition and its duality consequences.  The
monoidal and duality primitives are Mathlib's `MonoidalPreadditive` and
`ExactPairing`; the chapter-facing combined class only adds the finite-product
part of the source's additive-category hypothesis.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DirectSum

universe v u

namespace Formalization.Books.Homology.Unit17

/-! ## Additive monoidal categories -/

/-- An additive category equipped with a monoidal structure whose tensor is
additive in each variable.  `MonoidalPreadditive` is Mathlib's canonical
interface for the additivity of the two tensoring functors. -/
class AdditiveMonoidalCategory (C : Type u) [Category.{v} C]
    extends Formalization.Books.Homology.Unit03.AdditiveCategory C,
      MonoidalCategory C, MonoidalPreadditive C

instance additiveMonoidalCategory_to_additiveCategory
    (C : Type u) [Category.{v} C] [h : AdditiveMonoidalCategory C] :
    Formalization.Books.Homology.Unit03.AdditiveCategory C :=
  h.toAdditiveCategory

instance additiveMonoidalCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveMonoidalCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Duals and direct sums -/

/-- The direct sum of two left-dual pairs is again a left-dual pair. -/
theorem left_dual_biproduct
    {C : Type u} [Category.{v} C] [AdditiveMonoidalCategory C]
    {X₁ X₂ Y₁ Y₂ : C} [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂] :
    Nonempty (ExactPairing (X₁ ⊞ X₂) (Y₁ ⊞ Y₂)) := by
  sorry

/-- In a Karoubian additive monoidal category, both summands in a biproduct
decomposition of a left-dualizable object are left-dualizable. -/
theorem left_dual_of_biproduct_summand
    {C : Type u} [Category.{v} C] [AdditiveMonoidalCategory C]
    [IsIdempotentComplete C] {X Y X₁ X₂ : C} [ExactPairing X Y]
    (e : X ≅ X₁ ⊞ X₂) :
    (∃ Y₁ : C, Nonempty (ExactPairing X₁ Y₁)) ∧
      (∃ Y₂ : C, Nonempty (ExactPairing X₂ Y₂)) := by
  sorry

/- The Hom-set equalities and functorial Hom bijections displayed in the
   source proof are the chapter's existing `leftDualHomEquiv` API; the theorem
   above records the source assertion without duplicating those proof steps. -/

/-! ## Graded vector spaces -/

/-- The category of integer-graded `F`-vector spaces. -/
abbrev GradedVectorSpace (F : Type u) [Field F] :=
  GradedObject ℤ (ModuleCat.{u} F)

/-- The graded tensor product object, whose degree `n` component is the
coproduct of `Vᵖ ⊗ Wᑫ` over `p + q = n`. -/
noncomputable abbrev gradedTensor (F : Type u) [Field F]
    (V W : GradedVectorSpace F) [GradedObject.HasTensor V W] :
    GradedVectorSpace F := GradedObject.Monoidal.tensorObj V W

/-- The unit graded vector space, concentrated in degree zero. -/
noncomputable abbrev gradedTensorUnit (F : Type u) [Field F] : GradedVectorSpace F :=
  GradedObject.Monoidal.tensorUnit

/-- The degree-zero component of the graded tensor unit is the ordinary
`F`-vector-space tensor unit. -/
noncomputable def gradedTensorUnitZeroIso (F : Type u) [Field F] :
    (gradedTensorUnit F) 0 ≅ 𝟙_ (ModuleCat.{u} F) :=
  GradedObject.Monoidal.tensorUnit₀

/-- Every nonzero component of the graded tensor unit is the zero module. -/
noncomputable def gradedTensorUnitNonzeroInitial
    (F : Type u) [Field F] (n : ℤ) (hn : n ≠ 0) :
    IsInitial ((gradedTensorUnit F) n) :=
  GradedObject.Monoidal.isInitialTensorUnitApply n hn

/- The generic graded-object construction supplies the usual associativity
   constraint and unit constraints for graded vector spaces.  The direction is
   the one used in the source, namely `U ⊗ (V ⊗ W) ≅ (U ⊗ V) ⊗ W`. -/
noncomputable def gradedAssociator
    (F : Type u) [Field F] (U V W : GradedVectorSpace F)
    [GradedObject.HasTensor U V]
    [GradedObject.HasTensor (gradedTensor F U V) W]
    [GradedObject.HasTensor V W]
    [GradedObject.HasTensor U (gradedTensor F V W)]
    [GradedObject.HasGoodTensor₁₂Tensor U V W]
    [GradedObject.HasGoodTensorTensor₂₃ U V W] :
    gradedTensor F U (gradedTensor F V W) ≅
      gradedTensor F (gradedTensor F U V) W :=
  (GradedObject.Monoidal.associator U V W).symm

noncomputable def gradedLeftUnitor
    (F : Type u) [Field F] (V : GradedVectorSpace F)
    [∀ X : ModuleCat.{u} F,
      PreservesColimit (Functor.empty.{0} (ModuleCat.{u} F))
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} F)).flip.obj X)] :
    gradedTensor F (gradedTensorUnit F) V ≅ V :=
  GradedObject.Monoidal.leftUnitor V

noncomputable def gradedRightUnitor
    (F : Type u) [Field F] (V : GradedVectorSpace F)
    [∀ X : ModuleCat.{u} F,
      PreservesColimit (Functor.empty.{0} (ModuleCat.{u} F))
        ((MonoidalCategory.curriedTensor (ModuleCat.{u} F)).obj X)] :
    gradedTensor F V (gradedTensorUnit F) ≅ V :=
  GradedObject.Monoidal.rightUnitor V

noncomputable def gradedPlainCommutativity
    (F : Type u) [Field F] (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] :
    gradedTensor F V W ≅ gradedTensor F W V :=
  GradedObject.Monoidal.braiding V W

/-- The scalar appearing in the Koszul commutativity constraint. -/
def koszulSign (F : Type u) [Field F] (p q : ℤ) : F :=
  (-1 : F) ^ (p * q)

/-- The componentwise data expressing the signed commutativity constraint on
graded vector spaces.  The existence and coherence proof is left to the
theorem-statement stage, while the displayed component equation records the
source's precise sign convention. -/
structure GradedKoszulBraiding (F : Type u) [Field F]
    (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] where
  constraint : gradedTensor F V W ≅ gradedTensor F W V
  hom_on_component : ∀ (p q k : ℤ) (h : p + q = k),
    GradedObject.Monoidal.ιTensorObj V W p q k h ≫ constraint.hom k =
      (koszulSign F p q • (β_ (V p) (W q)).hom) ≫
        GradedObject.Monoidal.ιTensorObj W V q p k
          (by simpa only [add_comm] using h)

/- The source notes that both the unsigned and signed constraints satisfy the
   symmetric monoidal coherence diagrams. -/
structure GradedVectorSpaceSymmetricStructures (F : Type u) [Field F] where
  monoidal : MonoidalCategory (GradedVectorSpace F)
  unsigned : @SymmetricCategory (GradedVectorSpace F) _ monoidal
  signed : @SymmetricCategory (GradedVectorSpace F) _ monoidal

theorem graded_vector_space_monoidal_data
    (F : Type u) [Field F] :
    Nonempty (MonoidalCategory (GradedVectorSpace F)) := by
  sorry

theorem graded_vector_space_symmetric_structures
    (F : Type u) [Field F] :
    Nonempty (GradedVectorSpaceSymmetricStructures F) := by
  sorry

theorem graded_koszul_braiding_exists
    (F : Type u) [Field F] (V W : GradedVectorSpace F)
    [GradedObject.HasTensor V W] [GradedObject.HasTensor W V] :
    Nonempty (GradedKoszulBraiding F V W) := by
  sorry

/-! ## Duals of graded vector spaces -/

/-- The component pairings associated with a graded left-dual evaluation,
written as bilinear maps between opposite degrees, with injectivity in both
arguments. -/
structure GradedNondegeneratePairing (F : Type u) [Field F]
    (V W : GradedVectorSpace F) [MonoidalCategory (GradedVectorSpace F)]
    [ExactPairing V W] where
  pairing : ∀ n : ℤ, (W (-n) : Type u) →ₗ[F] Module.Dual F (V n : Type u)
  left_nondegenerate : ∀ n, Function.Injective (pairing n)
  right_nondegenerate : ∀ n, Function.Injective (LinearMap.flip (pairing n))

/-- If a graded vector space has a left dual, then it is finite-dimensional in
total degree and evaluation gives nondegenerate opposite-degree pairings. -/
theorem graded_left_dual_finite_and_nondegenerate
    (F : Type u) [Field F] [MonoidalCategory (GradedVectorSpace F)]
    {V W : GradedVectorSpace F} [ExactPairing V W] :
    Module.Finite F (⨁ n, (V n : Type u)) ∧
      Nonempty (GradedNondegeneratePairing F V W) := by
  sorry

end Formalization.Books.Homology.Unit17
