import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Yoneda

/-!
# Homological Algebra, Chapter 4: Karoubian categories

Mathlib's `IsIdempotentComplete` is the canonical interface for the
Karoubian condition.  In a preadditive category, Mathlib identifies it with
the existence of kernels for all idempotent endomorphisms.  The declarations
below record the source statements using that interface, together with the
countable-product argument's explicit presheaf and abelian-group maps.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive

universe v u

namespace Formalization.Books.Homology.Unit04

/-! ## Karoubian categories and the equivalent formulations -/

/- The source definition is Mathlib's `IsIdempotentComplete`; the following
   theorem exposes its preadditive kernel formulation under a chapter-local
   name. -/

theorem karoubian_iff_idempotents_have_kernels
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasKernel p :=
  Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C

theorem karoubian_iff_idempotents_have_cokernels
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasCokernel p := by
  sorry

/- In the decomposition below `b.bicone.snd ≫ b.bicone.inr` is the projection
   onto the second summand.  The displayed equation says that `p` becomes this
   projection after transporting along `e : Z ≅ b.bicone.pt`. -/

theorem karoubian_iff_idempotent_direct_sum_decomposition
    {C : Type u} [Category.{v} C] [Preadditive C] :
    IsIdempotentComplete C ↔
      ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p →
        ∃ (X Y : C) (b : BinaryBiproductData X Y) (e : Z ≅ b.bicone.pt),
          p ≫ e.hom = e.hom ≫ b.bicone.snd ≫ b.bicone.inr := by
  sorry

/-! ## The representability observation in the product argument -/

/- For `W : C`, this is the subgroup of morphisms `W ⟶ X` killed by `e`.
   Contravariance is implemented by precomposition. -/

def idempotentKernelPresheaf
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X : C) (e : X ⟶ X) : Cᵒᵖ ⥤ Type v where
  obj W := {f : W.unop ⟶ X // f ≫ e = 0}
  map := fun {W V} g =>
    TypeCat.ofHom (fun f : {f : W.unop ⟶ X // f ≫ e = 0} =>
      ⟨g.unop ≫ f.1, by
        simp only [Category.assoc, f.2, comp_zero]⟩)
  map_id := by
    intro W
    ext f
    simp
  map_comp := by
    intro W V U f g
    ext h
    simp [Category.assoc]

theorem idempotent_kernel_presheaf_isRepresentable_iff
    {C : Type u} [Category.{v} C] [Preadditive C]
    (X : C) (e : X ⟶ X) :
    (idempotentKernelPresheaf X e).IsRepresentable ↔ HasKernel e := by
  sorry

/-! ## The explicit countable-product maps on abelian groups -/

/- The product indexed by `ℕ` is represented by the function type `ℕ → A`. -/

def projectorPhi
    {A : Type u} [AddCommGroup A] (e : A →+ A) :
    (ℕ → A) →+ (ℕ → A) where
  toFun a n := e (a n) + (a (n + 1) - e (a (n + 1)))
  map_zero' := by
    funext n
    simp
  map_add' a b := by
    funext n
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

def projectorPsi
    {A : Type u} [AddCommGroup A] (e : A →+ A) :
    (ℕ → A) →+ (ℕ → A) where
  toFun a n :=
    match n with
    | 0 => a 0
    | n + 1 => (a n - e (a n)) + e (a (n + 1))
  map_zero' := by
    funext n
    cases n <;> simp
  map_add' a b := by
    funext n
    cases n <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/- The textbook writes an equality between kernels living in different
   ambient groups.  The source-faithful correction is the canonical additive
   isomorphism between them. -/

theorem projector_kernel_equiv
    {A : Type u} [AddCommGroup A] (e : A →+ A)
    (he : e.comp e = e) :
    Nonempty (e.ker ≃+ (projectorPhi e).ker) := by
  sorry

theorem projectorPhi_has_right_inverse
    {A : Type u} [AddCommGroup A] (e : A →+ A)
    (he : e.comp e = e) :
    Function.RightInverse (projectorPsi e) (projectorPhi e) := by
  sorry

/-! ## Countable products/coproducts force the Karoubian condition -/

theorem karoubian_of_countable_products_of_kernels_of_split_epimorphisms
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableProducts C]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitEpi f], HasKernel f) :
    IsIdempotentComplete C := by
  sorry

theorem karoubian_of_countable_coproducts_of_cokernels_of_split_monomorphisms
    {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableCoproducts C]
    (h : ∀ {X Y : C} (f : X ⟶ Y) [IsSplitMono f], HasCokernel f) :
    IsIdempotentComplete C := by
  sorry

end Formalization.Books.Homology.Unit04
