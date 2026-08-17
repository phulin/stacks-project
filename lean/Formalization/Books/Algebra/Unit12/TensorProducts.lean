import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import Formalization.Books.Algebra.Unit09.Localization

/-!
# Commutative Algebra, Chapter 12: Tensor products

The binary tensor product is Mathlib's `TensorProduct`, and the finite
multilinear tensor product is Mathlib's `PiTensorProduct`.  The declarations
below expose the book-facing interfaces while keeping the canonical
constructions and categorical APIs as the underlying objects.
-/

namespace Formalization.Books.Algebra.Unit12

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit09
open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Bilinear maps and the binary tensor product -/

/-- An `R`-bilinear map, represented by the canonical curried linear-map type. -/
abbrev BilinearMap (R M N P : Type*) [CommRing R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] :=
  M →ₗ[R] N →ₗ[R] P

/-- The universal property of a binary tensor product, in pointwise form. -/
def IsTensorProduct {R M N T : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T]
    [Module R M] [Module R N] [Module R T]
    (g : BilinearMap R M N T) : Prop :=
  ∀ (P : Type*) [AddCommGroup P] [Module R P]
    (f : BilinearMap R M N P),
    ∃! F : T →ₗ[R] P, ∀ m n, F (g m n) = f m n

/-- The canonical bilinear map into `M ⊗[R] N`. -/
def tensorProductCanonicalMap {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    BilinearMap R M N (TensorProduct R M N) :=
  TensorProduct.mk R M N

/-- The lifting and uniqueness part of the tensor-product universal property. -/
theorem tensorProduct_lift_unique {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : BilinearMap R M N P) :
    ∃! F : TensorProduct R M N →ₗ[R] P,
      ∀ m n, F (m ⊗ₜ[R] n) = f m n := by
  refine ⟨TensorProduct.lift f, ?_, ?_⟩
  · intro m n
    rfl
  · intro F hF
    exact TensorProduct.lift.unique hF

theorem tensorProduct_isTensorProduct {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    IsTensorProduct (tensorProductCanonicalMap (R := R) (M := M) (N := N)) := by
  intro P _ _ f
  exact tensorProduct_lift_unique f

/- The source's quotient construction is represented by Mathlib's tensor
   product; the following exact theorem records its generation assertion. -/
theorem tensorProduct_pure_tensors_span {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    Submodule.span R
        {t : TensorProduct R M N | ∃ m n, m ⊗ₜ[R] n = t} = ⊤ := by
  exact TensorProduct.span_tmul_eq_top R M N

/-- Two tensor-product universal maps are uniquely isomorphic. -/
theorem tensorProduct_universal_unique {R M N T T' : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup T] [AddCommGroup T']
    [Module R M] [Module R N] [Module R T] [Module R T']
    (g : BilinearMap R M N T) (g' : BilinearMap R M N T')
    (hg : IsTensorProduct g) (hg' : IsTensorProduct g') :
    ∃! e : T ≃ₗ[R] T', ∀ m n, e (g m n) = g' m n := by
  sorry

/-! ## Symmetries, products, units, and multilinear tensor products -/

/-- The flip isomorphism `M ⊗ N ≅ N ⊗ M`. -/
def tensorProductFlip {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    TensorProduct R M N ≃ₗ[R] TensorProduct R N M :=
  TensorProduct.comm R M N

@[simp] theorem tensorProductFlip_tmul {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (m : M) (n : N) :
    tensorProductFlip (R := R) (M := M) (N := N) (m ⊗ₜ[R] n) = n ⊗ₜ[R] m := by
  rfl

/- In `ModuleCat`, the binary biproduct has underlying module `M × N`; this
   is the canonical Mathlib representative of the displayed `M ⊕ N`. -/
def tensorProductBiproduct {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct R (M × N) P ≃ₗ[R]
      (TensorProduct R M P) × (TensorProduct R N P) :=
  TensorProduct.prodLeft R R M N P

@[simp] theorem tensorProductBiproduct_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (m : M) (n : N) (p : P) :
    tensorProductBiproduct (R := R) (M := M) (N := N) (P := P)
        ((m, n) ⊗ₜ[R] p) = (m ⊗ₜ[R] p, n ⊗ₜ[R] p) := by
  rfl

/-- The unit isomorphism `R ⊗[R] M ≅ M`. -/
def tensorProductUnit {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] :
    TensorProduct R R M ≃ₗ[R] M :=
  TensorProduct.lid R M

@[simp] theorem tensorProductUnit_tmul {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (r : R) (m : M) :
    tensorProductUnit (R := R) (M := M) (r ⊗ₜ[R] m) = r • m := by
  rfl

/-- Mathlib's multilinear tensor product for a finite family of modules. -/
abbrev multilinearTensorProduct {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    Type (max u v) :=
  PiTensorProduct R M

/-- The universal multilinear map into the multilinear tensor product. -/
def multilinearTensorProductMap {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    MultilinearMap R M (multilinearTensorProduct (R := R) M) :=
  PiTensorProduct.tprod R

/-- The universal property of a multilinear tensor product. -/
def IsMultilinearTensorProduct {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (T : Type w) [AddCommGroup T] [Module R T]
    (g : MultilinearMap R M T) : Prop :=
  ∀ (P : Type*) [AddCommGroup P] [Module R P]
    (f : MultilinearMap R M P),
    ∃! F : T →ₗ[R] P, ∀ x, F (g x) = f x

theorem multilinearTensorProduct_isUniversal {R : Type u} [CommRing R] {r : ℕ}
    (M : Fin r → Type v) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] :
    IsMultilinearTensorProduct M
      (multilinearTensorProduct (R := R) M)
      (multilinearTensorProductMap (R := R) M) := by
  intro P _ _ f
  refine ⟨PiTensorProduct.lift f, ?_, ?_⟩
  · intro x
    change PiTensorProduct.lift f (PiTensorProduct.tprod R x) = f x
    exact PiTensorProduct.lift.tprod x
  · intro F hF
    exact PiTensorProduct.lift.unique hF

theorem multilinearTensorProduct_pure_tensors_span {R : Type u} [CommRing R]
    {r : ℕ} (M : Fin r → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] :
    Submodule.span R
        (Set.range (multilinearTensorProductMap (R := R) M)) = ⊤ :=
  PiTensorProduct.span_tprod_eq_top (R := R) (s := M)

theorem multilinearTensorProduct_universal_unique {R : Type u} [CommRing R]
    {r : ℕ} (M : Fin r → Type v) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] {T T' : Type*} [AddCommGroup T] [AddCommGroup T']
    [Module R T] [Module R T'] (g : MultilinearMap R M T)
    (g' : MultilinearMap R M T')
    (hg : IsMultilinearTensorProduct M T g)
    (hg' : IsMultilinearTensorProduct M T' g') :
    ∃! e : T ≃ₗ[R] T', ∀ x, e (g x) = g' x := by
  sorry

/-- The canonical associator for three binary tensor products. -/
def tensorProductAssociator {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    TensorProduct R (TensorProduct R M N) P ≃ₗ[R]
      TensorProduct R M (TensorProduct R N P) :=
  TensorProduct.assoc R M N P

@[simp] theorem tensorProductAssociator_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (m : M) (n : N) (p : P) :
    tensorProductAssociator (R := R) (M := M) (N := N) (P := P)
        ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = m ⊗ₜ[R] (n ⊗ₜ[R] p) := by
  rfl

/-! ## Bimodules and the Hom adjunction -/

/-- Two commuting module actions, the commutative-ring form of a bimodule. -/
def IsBimodule (A B N : Type*) [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N] : Prop :=
  SMulCommClass A B N

/-- The right-action notation for a bimodule, expressed using the left action of `B`. -/
def bimoduleRightAction {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N] : N → B → N :=
  fun n b => b • n

theorem bimodule_right_action_commutes {A B N : Type*} [CommRing A] [CommRing B]
    [AddCommGroup N] [Module A N] [Module B N]
    (hN : IsBimodule A B N) (a : A) (b : B) (n : N) :
    bimoduleRightAction (A := A) (B := B) (N := N) (a • n) b =
      a • bimoduleRightAction (A := A) (B := B) (N := N) n b := by
  exact (hN.smul_comm a b n).symm

/- The action on a tensor product in which the `B`-action is on the right
   factor is obtained by flipping, transporting the `B`-module structure, and
   flipping back.  This is the canonical construction needed for the
   bimodule lemma and has no extra mathematical hypotheses. -/
@[instance_reducible] noncomputable def tensorProductBModule
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] : Module B (TensorProduct A X Y) :=
  (TensorProduct.comm A X Y).toAddEquiv.module B

/- These interfaces express that the transported action commutes with the
   original `A`-action.  They are useful named facts for the two nested
   tensor products and are proved in the later proof stage. -/
theorem tensorProductBModule_smulCommClass
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] :
    letI : Module B (TensorProduct A X Y) :=
      tensorProductBModule A B X Y
    SMulCommClass A B (TensorProduct A X Y) := by
  sorry

theorem tensorProductBModule_smulCommClass_symm
    (A B X Y : Type*) [CommRing A] [CommRing B]
    [AddCommGroup X] [AddCommGroup Y]
    [Module A X] [Module A Y] [Module B Y]
    [SMulCommClass A B Y] :
    letI : Module B (TensorProduct A X Y) :=
      tensorProductBModule A B X Y
    SMulCommClass B A (TensorProduct A X Y) := by
  sorry

/- The tensor-with-bimodule assertion uses the induced actions above. -/
theorem tensor_with_bimodule {A B M N P : Type*} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module B N] [Module B P]
    (hN : IsBimodule A B N) :
    letI : SMulCommClass A B N := hN
    letI : SMulCommClass B A N := SMulCommClass.symm A B N
    letI : Module B (TensorProduct A M N) :=
      tensorProductBModule A B M N
    letI : SMulCommClass A B (TensorProduct A M N) :=
      tensorProductBModule_smulCommClass A B M N
    letI : SMulCommClass B A (TensorProduct A M N) :=
      tensorProductBModule_smulCommClass_symm A B M N
    letI : SMulCommClass A B (TensorProduct B N P) := inferInstance
    letI : Module B (TensorProduct A M (TensorProduct B N P)) :=
      tensorProductBModule A B M (TensorProduct B N P)
    letI : SMulCommClass A B (TensorProduct A M (TensorProduct B N P)) :=
      tensorProductBModule_smulCommClass A B M (TensorProduct B N P)
    IsBimodule A B ((TensorProduct A M N) ⊗[B] P) ∧
      IsBimodule A B (TensorProduct A M (TensorProduct B N P)) ∧
      Nonempty
        ((TensorProduct A M N) ⊗[B] P ≃ₗ[A]
          TensorProduct A M (TensorProduct B N P)) := by
  sorry

/-- The tensor/Hom adjunction for modules. -/
noncomputable def tensorHomEquiv {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] :
    (TensorProduct R M N →ₗ[R] P) ≃ₗ[R]
      (M →ₗ[R] N →ₗ[R] P) :=
  (TensorProduct.lift.equiv (RingHom.id R) M N P).symm

@[simp] theorem tensorHomEquiv_apply_tmul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (F : TensorProduct R M N →ₗ[R] P) (m : M) (n : N) :
    tensorHomEquiv (R := R) (M := M) (N := N) (P := P) F m n =
      F (m ⊗ₜ[R] n) := by
  rfl

/-! ## Colimits and exactness -/

/-- The colimit diagram obtained by tensoring a module-valued diagram on the right. -/
abbrev tensorProductColimitDiagram {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) : I ⥤ ModuleCat.{u} R :=
  M ⋙ MonoidalCategory.tensorRight N

/-- Tensoring with a fixed module commutes with colimits in `ModuleCat`. -/
noncomputable def tensorProductColimitIso {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) :
    colimit (tensorProductColimitDiagram M N) ≅
      (MonoidalCategory.tensorRight N).obj (colimit M) :=
  (preservesColimitIso (MonoidalCategory.tensorRight N) M).symm

/-- The canonical map from a stage tensor product to the tensor product of the colimit. -/
def tensorProductColimitStageMap {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (i : I) :
    (tensorProductColimitDiagram M N).obj i ⟶
      (MonoidalCategory.tensorRight N).obj (colimit M) :=
  (MonoidalCategory.tensorRight N).map (colimit.ι M i)

theorem tensorProductColimitIso_stage {R : Type u} [CommRing R]
    {I : Type u} [Preorder I] (M : I ⥤ ModuleCat.{u} R)
    (N : ModuleCat.{u} R) (i : I) :
    colimit.ι (tensorProductColimitDiagram M N) i ≫
        (tensorProductColimitIso M N).hom =
      tensorProductColimitStageMap M N i := by
  exact ι_preservesColimitIso_inv (MonoidalCategory.tensorRight N) M i

/-- Tensoring an exact right-exact sequence remains exact and surjective. -/
theorem tensorProduct_right_exact {R M₁ M₂ M₃ N : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup N]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) ∧
      Function.Surjective (LinearMap.rTensor N g) := by
  exact ⟨rTensor_exact N hfg hg, LinearMap.rTensor_surjective N hg⟩

/-- A map ending in zero is represented by exactness together with surjectivity. -/
theorem tensorProduct_right_exact_sequence {R M₁ M₂ M₃ N : Type*} [CommRing R]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup N]
    [Module R M₁] [Module R M₂] [Module R M₃] [Module R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) ∧
      Function.Surjective (LinearMap.rTensor N g) :=
  tensorProduct_right_exact f g hfg hg

/- The following explicit example records the source's failure of left
   exactness; the displayed calculation is the pure-tensor form of the
   vanishing induced map. -/
def integerDoubling : ℤ →ₗ[ℤ] ℤ :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight 2

theorem integerDoubling_injective : Function.Injective integerDoubling := by
  sorry

theorem integer_tensor_zmod_two_nontrivial :
    Nontrivial (TensorProduct ℤ ℤ (ZMod 2)) := by
  exact (TensorProduct.lid ℤ (ZMod 2)).surjective.nontrivial

theorem integerDoubling_rTensor_zmod_two_zero :
    LinearMap.rTensor (ZMod 2) integerDoubling = 0 := by
  sorry

theorem integerDoubling_rTensor_zmod_two_not_injective :
    ¬Function.Injective (LinearMap.rTensor (ZMod 2) integerDoubling) := by
  sorry

theorem integerDoubling_rTensor_zmod_two_pure_zero (x : ℤ) (y : ZMod 2) :
    LinearMap.rTensor (ZMod 2) integerDoubling (x ⊗ₜ[ℤ] y) = 0 := by
  sorry

/-- The canonical Mathlib flatness predicate used by the book's definition. -/
abbrev FlatModule (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :=
  Module.Flat R M

theorem flatModule_preserves_exact {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] [FlatModule R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hfg : Function.Exact f g) :
    Function.Exact (LinearMap.rTensor P f) (LinearMap.rTensor P g) := by
  exact Module.Flat.rTensor_exact P hfg

/-! ## Finiteness and localization -/

theorem tensorProduct_finite {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (TensorProduct R M N) := by
  infer_instance

theorem tensorProduct_finitePresentation {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (TensorProduct R M N) := by
  sorry

/-- The canonical localization/module-tensor equivalence. -/
noncomputable def tensorProductLocalizationModuleEquiv
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    localization S ⊗[R] M ≃ₗ[localization S] localizedModule S M :=
  (LocalizedModule.equivTensorProduct S M).symm

@[simp] theorem tensorProductLocalizationModuleEquiv_tmul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) (a : R) (m : M) (s : S) :
    tensorProductLocalizationModuleEquiv S
        (Localization.mk a s ⊗ₜ[R] m) =
      a • localizedModuleFraction S m s := by
  exact LocalizedModule.equivTensorProduct_symm_apply_tmul S m a s

/-- The canonical localization equivalence for a tensor product of two modules. -/
noncomputable def tensorProductLocalizationEquiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) :
    localizedModule S M ⊗[localization S] localizedModule S N ≃ₗ[localization S]
      localizedModule S (TensorProduct R M N) :=
  (TensorProduct.congr
      (LocalizedModule.equivTensorProduct (R := R) S M)
      (LocalizedModule.equivTensorProduct (R := R) S N)) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange R (localization S) M N).symm ≪≫ₗ
      (LocalizedModule.equivTensorProduct (R := R) S (TensorProduct R M N)).symm

@[simp] theorem tensorProductLocalizationEquiv_tmul
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (S : Submonoid R) (m : M) (n : N) (s t : S) :
    tensorProductLocalizationEquiv S
        (localizedModuleFraction S m s ⊗ₜ[localization S]
          localizedModuleFraction S n t) =
      localizedModuleFraction S (m ⊗ₜ[R] n) (s * t) := by
  sorry

end
end Formalization.Books.Algebra.Unit12
