import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.RingTheory.PicardGroup

/-!
# More on Algebra, Chapter 118: Picard groups of rings

The canonical Mathlib definitions `Module.Invertible` and `CommRing.Pic` are
used for invertible modules and the Picard group.  The declarations below
record the source-facing characterizations and the UFD calculation.
-/

namespace Formalization.Books.MoreAlgebra.Unit118

open scoped TensorProduct

universe u v

noncomputable section

/-! ## Invertible modules -/

/- The source's phrase “trivial invertible module” is represented by the
canonical proposition `Nonempty (M ≃ₗ[R] R)`. -/

/-- An inverse module in the sense of the source's condition (3). -/
def HasTensorInverse
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∃ N : ModuleCat.{max u v} R,
    Nonempty (M ⊗[R] N ≃ₗ[R] R)

/-- The three conditions in the source's characterization of invertible modules. -/
def invertibleModuleConditions
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : List Prop :=
  [Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R M 1,
    Module.Invertible R M,
    HasTensorInverse R M]

/-- Finite locally free modules of rank one are precisely the invertible modules. -/
theorem finiteLocallyFreeOfRank_one_iff_invertible
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R M 1 ↔
      Module.Invertible R M := by
  sorry

/-- A module is invertible precisely when it has a tensor inverse. -/
theorem invertible_iff_hasTensorInverse
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.Invertible R M ↔ HasTensorInverse R M := by
  constructor
  · intro hM
    let _ : Module.Invertible R M := hM
    refine ⟨ModuleCat.of R (Module.Dual R M), ?_⟩
    exact ⟨TensorProduct.comm R M (Module.Dual R M) ≪≫ₗ
      Module.Invertible.linearEquiv R M⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact Module.Invertible.left e

/-- The three conditions in the source's lemma are equivalent. -/
theorem invertibleModuleConditions_tfae
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] :
    List.TFAE (invertibleModuleConditions R M) := by
  sorry

/-- Any tensor inverse is isomorphic to the dual module. -/
theorem tensorInverse_equiv_dual
    {R : Type u} {M : Type v} {N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ⊗[R] N ≃ₗ[R] R) :
    Nonempty (N ≃ₗ[R] Module.Dual R M) := by
  exact ⟨Module.Invertible.linearEquivDual
    (TensorProduct.comm R N M ≪≫ₗ e)⟩

/-- Triviality of an invertible module is the same as freeness. -/
theorem trivial_invertible_iff_free
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Invertible R M] :
    Nonempty (M ≃ₗ[R] R) ↔ Module.Free R M :=
  Module.Invertible.free_iff_linearEquiv.symm

/-! ## The Picard group -/

/- The source's `Pic(R)` is Mathlib's `CommRing.Pic R`.  Its `CommGroup`
instance, tensor-product multiplication, identity, and dual inverse are
already provided by `Mathlib.RingTheory.PicardGroup`; the following
source-facing statements expose those operations together. -/

/-- The class of a tensor product is the product of the classes. -/
theorem picard_class_tensor
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M]
    [AddCommGroup N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
  CommRing.Pic.mk_tensor

/-- The inverse class is represented by the dual module. -/
theorem picard_class_dual
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
  CommRing.Pic.mk_dual

/-- The free rank-one module represents the identity in the Picard group. -/
theorem picard_class_ring (R : Type u) [CommRing R] :
    CommRing.Pic.mk R R = 1 :=
  CommRing.Pic.mk_self

/-- A Picard class is the identity precisely when its module is trivial. -/
theorem picard_class_eq_one_iff_trivial
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R M = 1 ↔ Nonempty (M ≃ₗ[R] R) :=
  CommRing.Pic.mk_eq_one_iff

/-! ## UFDs -/

/-- The Picard group of a unique factorization domain is trivial. -/
theorem picard_group_subsingleton_of_ufd
    (R : Type u) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] :
    Subsingleton (CommRing.Pic R) := by
  infer_instance

end

end Formalization.Books.MoreAlgebra.Unit118
