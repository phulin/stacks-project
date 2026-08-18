import Formalization.Books.Algebra.Unit88.MittagLefflerModules
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Data.PNat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Commutative Algebra, Chapter 89: Interchanging direct products with tensor

The canonical product--tensor map is Mathlib's `TensorProduct.piRightHom`.
The Mittag--Leffler predicate and universal exactness are the canonical
interfaces from Chapters 88 and 82, respectively.
-/

namespace Formalization.Books.Algebra.Unit89

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Categories.Unit21
open scoped DirectSum TensorProduct

universe u v w z

noncomputable section

/-! ## The canonical map and the examples -/

/- The source's notation `M^A` is the ordinary product of copies of `M`. -/
abbrev modulePower (M : Type u) (A : Type v) := A → M

/-- The canonical map from tensoring a product to the product of tensors. -/
def productTensorMap
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (Q : A → ModuleCat.{z} R) :
    TensorProduct R (M : Type w) (∀ a, (Q a : Type z)) →ₗ[R]
      ∀ a, TensorProduct R (M : Type w) (Q a : Type z) :=
  TensorProduct.piRightHom R R (M : Type w) (fun a => (Q a : Type z))

@[simp]
theorem productTensorMap_tmul
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (Q : A → ModuleCat.{z} R)
    (m : (M : Type w)) (q : ∀ a, (Q a : Type z)) :
    productTensorMap M Q (m ⊗ₜ[R] q) = fun a => m ⊗ₜ[R] q a := by
  rfl

/-- The canonical map `M ⊗ R^A → M^A`, using `M ⊗ R ≅ M` in each factor. -/
def tensorModulePowerMap
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) :
    TensorProduct R (M : Type w) (modulePower R A) →ₗ[R]
      modulePower (M : Type w) A :=
  (LinearEquiv.piCongrRight (fun _ => TensorProduct.rid R (M : Type w))).toLinearMap.comp
    (productTensorMap M (fun _ : A => ModuleCat.of R R))

@[simp]
theorem tensorModulePowerMap_tmul
    {R : Type u} [CommRing R] {A : Type v}
    (M : ModuleCat.{w} R) (m : (M : Type w)) (q : modulePower R A) :
    tensorModulePowerMap M (m ⊗ₜ[R] q) = fun a => q a • m := by
  ext a
  simp [tensorModulePowerMap, productTensorMap]

/- The first example uses the positive natural numbers as the indexing set,
   so `ZMod n` agrees with the source's `Z/n` for every index. -/

def rationalModule : ModuleCat ℤ := ModuleCat.of ℤ ℚ

def integerQuotientFamily : ℕ+ → ModuleCat ℤ :=
  fun n => ModuleCat.of ℤ (ZMod (n : ℕ))

def integerDiagonalToQuotientProduct :
    ℤ →ₗ[ℤ] ∀ n : ℕ+, ZMod (n : ℕ) :=
  LinearMap.pi (fun n => (Int.castAddHom (ZMod (n : ℕ))).toIntLinearMap)

theorem integerDiagonalToQuotientProduct_injective :
    Function.Injective integerDiagonalToQuotientProduct := by
  sorry

def rationalTensorIntegerDiagonal :
    ℚ →ₗ[ℤ] TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ)) :=
  (integerDiagonalToQuotientProduct.lTensor ℚ).comp
    (TensorProduct.rid ℤ ℚ).symm.toLinearMap

theorem rationalTensorIntegerDiagonal_injective :
    Function.Injective rationalTensorIntegerDiagonal := by
  sorry

def rationalQuotientTensorMap :
    TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ)) →ₗ[ℤ]
      ∀ n : ℕ+, TensorProduct ℤ ℚ (ZMod (n : ℕ)) :=
  productTensorMap rationalModule integerQuotientFamily

theorem rationalQuotientTensorProduct_nontrivial :
    Nontrivial (TensorProduct ℤ ℚ (∀ n : ℕ+, ZMod (n : ℕ))) := by
  sorry

theorem rationalQuotientTensorProduct_subsingleton :
    Subsingleton (∀ n : ℕ+, TensorProduct ℤ ℚ (ZMod (n : ℕ))) := by
  sorry

theorem rationalQuotientTensorMap_not_injective :
    ¬Function.Injective rationalQuotientTensorMap := by
  sorry

def integerFamily : ℕ+ → ModuleCat ℤ :=
  fun _ => ModuleCat.of ℤ ℤ

def integerProductTensorEquiv :
    (∀ _ : ℕ+, TensorProduct ℤ ℚ ℤ) ≃ₗ[ℤ] ∀ _ : ℕ+, ℚ :=
  LinearEquiv.piCongrRight (fun _ => TensorProduct.rid ℤ ℚ)

def rationalIntegerProductTensorMap :
    TensorProduct ℤ ℚ (∀ _ : ℕ+, ℤ) →ₗ[ℤ] ∀ _ : ℕ+, ℚ :=
  integerProductTensorEquiv.toLinearMap.comp
    (productTensorMap rationalModule integerFamily)

def commonDenominatorSequences {A : Type v} : Set (A → ℚ) :=
  {x | ∃ m : ℤ, m ≠ 0 ∧ ∀ a, ∃ z : ℤ, x a = (z : ℚ) / (m : ℚ)}

theorem rationalIntegerProductTensorMap_range :
    Set.range rationalIntegerProductTensorMap =
      commonDenominatorSequences (A := ℕ+) := by
  sorry

theorem rationalIntegerProductTensorMap_not_surjective :
    ¬Function.Surjective rationalIntegerProductTensorMap := by
  sorry

/-! ## Finitely generated and finitely presented modules -/

/-- The four equivalent criteria for finite generation from Proposition 89.1. -/
theorem finite_generation_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      Module.Finite R (M : Type w),
      ∀ (A : Type v) (Q : A → ModuleCat.{z} R),
        Function.Surjective (productTensorMap M Q),
      ∀ (Q : ModuleCat.{z} R) (A : Type v),
        Function.Surjective (productTensorMap M (fun _ : A => Q)),
      ∀ (A : Type v), Function.Surjective (tensorModulePowerMap M (A := A))
    ] := by
  sorry

/-- The four equivalent criteria for finite presentation from Proposition 89.2. -/
theorem finite_presentation_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      Module.FinitePresentation R (M : Type w),
      ∀ (A : Type v) (Q : A → ModuleCat.{z} R),
        Function.Bijective (productTensorMap M Q),
      ∀ (Q : ModuleCat.{z} R) (A : Type v),
        Function.Bijective (productTensorMap M (fun _ : A => Q)),
      ∀ (A : Type v), Function.Bijective (tensorModulePowerMap M (A := A))
    ] := by
  sorry

/-- Tensor-kernel elements for finitely presented source modules factor through
    a finitely presented intermediate module (Lemma 89.3). -/
theorem kernel_tensored_finitelyPresented
    {R : Type u} [CommRing R] (M P Q : ModuleCat.{w} R)
    (hP : Module.FinitePresentation R (P : Type w))
    (f : (P : Type w) →ₗ[R] (M : Type w))
    (x : TensorProduct R (P : Type w) (Q : Type w))
    (hx : x ∈ LinearMap.ker (f.rTensor (Q : Type w))) :
    ∃ P' : ModuleCat.{w} R,
      Module.FinitePresentation R (P' : Type w) ∧
        ∃ f' : (P : Type w) →ₗ[R] (P' : Type w),
          (∃ g : (P' : Type w) →ₗ[R] (M : Type w), f = g.comp f') ∧
            x ∈ LinearMap.ker (f'.rTensor (Q : Type w)) := by
  sorry

/-- The tensor-product characterization of Mittag--Leffler modules
    (Proposition 89.4). -/
theorem mittagLeffler_tensor_iff
    {R : Type u} [CommRing R] (M : ModuleCat.{w} R) :
    List.TFAE [
      IsMittagLefflerModule M,
      ∀ (A : Type v) (Q : A → ModuleCat.{z} R),
        Function.Injective (productTensorMap M Q)
    ] := by
  sorry

/-! ## Permanence lemmas -/

/-- The predicate that an element of `F ⊗ M` comes from `F' ⊗ M`. -/
def tensorProductContains
    {R F M : Type u} [CommRing R]
    [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]
    (F' : Submodule R F) (x : TensorProduct R F M) : Prop :=
  ∃ y : TensorProduct R (F' : Type u) M,
    F'.subtype.rTensor M y = x

/- The smallest submodule in Lemma 89.5 is expressed by `IsLeast` in the
   complete lattice of submodules. -/
theorem minimal_tensor_submodule
    {R F M : Type u} [CommRing R]
    [AddCommGroup F] [AddCommGroup M] [Module R F] [Module R M]
    (hflat : Module.Flat R M)
    (hML : IsMittagLefflerModule (ModuleCat.of R M))
    (x : TensorProduct R F M) :
    ∃ F' : Submodule R F,
      IsLeast {G : Submodule R F | tensorProductContains G x} F' ∧
        Module.Finite R (F' : Type u) := by
  sorry

/-- In a universally exact sequence, Mittag--Lefflerness descends to the
    submodule and ascends from both ends (Lemma 89.6). -/
theorem pure_submodule_mittagLeffler
    {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{w} R}
    (f₁ : (M₁ : Type w) →ₗ[R] (M₂ : Type w))
    (f₂ : (M₂ : Type w) →ₗ[R] (M₃ : Type w))
    (hseq : universallyExact f₁ f₂) :
    (IsMittagLefflerModule M₂ → IsMittagLefflerModule M₁) ∧
      ((IsMittagLefflerModule M₁ ∧ IsMittagLefflerModule M₃) →
        IsMittagLefflerModule M₂) := by
  sorry

/-- A quotient by a finitely generated submodule of a Mittag--Leffler module is
    Mittag--Leffler (Lemma 89.7). -/
theorem quotient_module_mittagLeffler
    {R : Type u} [CommRing R] {M₁ M₂ M₃ : ModuleCat.{w} R}
    (f₁ : (M₁ : Type w) →ₗ[R] (M₂ : Type w))
    (f₂ : (M₂ : Type w) →ₗ[R] (M₃ : Type w))
    (hexact : Function.Exact f₁ f₂)
    (hsurj : Function.Surjective f₂)
    (hfinite : Module.Finite R (M₁ : Type w))
    (hML : IsMittagLefflerModule M₂) :
    IsMittagLefflerModule M₃ := by
  sorry

/-- A directed colimit of Mittag--Leffler modules with universally injective
    transition maps is Mittag--Leffler (Lemma 89.8). -/
theorem colimit_mittagLeffler_of_universallyInjective
    {R : Type u} [CommRing R] {I : Type v} [Preorder I]
    [Nonempty I] [IsDirectedOrder I] {M : ModuleCat.{w} R}
    (P : ColimitPresentation I M)
    (hstage : ∀ i, IsMittagLefflerModule (P.diag.obj i))
    (htrans : ∀ {i j : I} (hij : i ≤ j),
      universallyInjective ((P.diag.map (homOfLE hij)).hom)) :
    IsMittagLefflerModule M := by
  sorry

/-- A direct sum is Mittag--Leffler exactly when each summand is
    Mittag--Leffler (Lemma 89.9). -/
theorem directSum_mittagLeffler_iff
    {R : Type u} [CommRing R] {I : Type v}
    (M : I → ModuleCat.{w} R) :
    IsMittagLefflerModule
        (ModuleCat.of R (⨁ i, (M i : Type w))) ↔
      ∀ i, IsMittagLefflerModule (M i) := by
  sorry

/-- Flat Mittag--Leffler modules over a Mittag--Leffler ring module remain
    Mittag--Leffler after restriction of scalars (Lemma 89.10). -/
theorem flat_mittagLeffler_of_mittagLeffler_restrictScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{w} S)
    (hS : IsMittagLefflerModule
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)))
    (hflat : Module.Flat S (M : Type w))
    (hM : IsMittagLefflerModule M) :
    IsMittagLefflerModule ((ModuleCat.restrictScalars f).obj M) := by
  sorry

end

end Formalization.Books.Algebra.Unit89
