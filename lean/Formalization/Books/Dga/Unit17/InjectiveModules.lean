import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Differential Graded Algebra, Chapter 17: Injective modules over algebras

The source chapter uses right and left modules over a possibly noncommutative
algebra.  Mathlib's `ModuleCat` is the category of left modules, so right
`A`-modules are represented by `ModuleCat (Aᵐᵒᵖ)`.  The additive character
dual and the cogenerator `ℚ / ℤ` are reused from the earlier formalization of
injective modules.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Categories.Unit23
open Formalization.Books.MoreAlgebra.Unit55

universe u

namespace Formalization.Books.Dga.Unit17

/-! ## Left and right module conventions -/

/-- The category of right modules over `A`, represented as left modules over
the opposite ring. -/
abbrev RightModule (A : Type u) [Ring A] := ModuleCat.{u} Aᵐᵒᵖ

/-- The category of left modules over `A`. -/
abbrev LeftModule (A : Type u) [Ring A] := ModuleCat.{u} A

/-! ## Character duals and their actions -/

/- `CharacterDual` from More on Algebra is specialized to characters in one
   universe.  The module categories below are universe polymorphic, so use the
   same additive character dual with the target `ℚ / ℤ` in its canonical small
   universe. -/
abbrev DgaCharacterDual (M : Type u) [AddCommGroup M] := M →+ RationalModInteger

/-- The left `A`-module structure on the character dual of a right module.

For `a : A`, the scalar `MulOpposite.op a` acts on a right module as right
multiplication by `a`; hence this is the source formula
`(a f) x = f (x a)`. -/
instance leftCharacterDualModule {A M : Type u} [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] :
    Module A (DgaCharacterDual M) where
  smul a φ :=
    { toFun := fun x => φ (MulOpposite.op a • x)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  one_smul φ := by
    ext x
    change φ (MulOpposite.op (1 : A) • x) = φ x
    simp
  mul_smul a b φ := by
    ext x
    change φ (MulOpposite.op (a * b) • x) =
      φ (MulOpposite.op b • (MulOpposite.op a • x))
    rw [MulOpposite.op_mul, smul_smul]
  smul_zero a := by
    ext x
    change (0 : RationalModInteger) = 0
    rfl
  smul_add a φ ψ := by
    ext x
    change (φ + ψ) (MulOpposite.op a • x) =
      φ (MulOpposite.op a • x) + ψ (MulOpposite.op a • x)
    rfl
  add_smul a b φ := by
    ext x
    change φ (MulOpposite.op (a + b) • x) =
      φ (MulOpposite.op a • x) + φ (MulOpposite.op b • x)
    rw [MulOpposite.op_add, add_smul, map_add]
  zero_smul φ := by
    ext x
    change φ (MulOpposite.op (0 : A) • x) = 0
    simp

/-- The right `A`-module structure on the character dual of a left module. -/
instance rightCharacterDualModule {A M : Type u} [Ring A]
    [AddCommGroup M] [Module A M] :
    Module Aᵐᵒᵖ (DgaCharacterDual M) where
  smul b φ :=
    { toFun := fun x => φ (b.unop • x)
      map_zero' := by simp
      map_add' := by
        intro x y
        simp }
  one_smul φ := by
    ext x
    change φ ((1 : Aᵐᵒᵖ).unop • x) = φ x
    simp
  mul_smul a b φ := by
    ext x
    change φ ((a * b).unop • x) = φ (b.unop • (a.unop • x))
    rw [MulOpposite.unop_mul, smul_smul]
  smul_zero a := by
    ext x
    change (0 : RationalModInteger) = 0
    rfl
  smul_add a φ ψ := by
    ext x
    change (φ + ψ) (a.unop • x) = φ (a.unop • x) + ψ (a.unop • x)
    rfl
  add_smul a b φ := by
    ext x
    change φ ((a + b).unop • x) = φ (a.unop • x) + φ (b.unop • x)
    rw [MulOpposite.unop_add, add_smul, map_add]
  zero_smul φ := by
    ext x
    change φ ((0 : Aᵐᵒᵖ).unop • x) = 0
    simp

/-- The character dual of a right `A`-module, as a left `A`-module. -/
def leftDual (A : Type u) [Ring A] (M : RightModule A) : LeftModule A :=
  ModuleCat.of A (DgaCharacterDual (M : Type u))

/-- The character dual of a left `A`-module, as a right `A`-module. -/
def rightDual (A : Type u) [Ring A] (M : LeftModule A) : RightModule A :=
  ModuleCat.of Aᵐᵒᵖ (DgaCharacterDual (M : Type u))

@[simp] theorem leftDual_smul_apply {A : Type u} [Ring A]
    (M : RightModule A) (a : A) (φ : DgaCharacterDual (M : Type u)) (x : M) :
    (a • φ) x = φ (MulOpposite.op a • x) := rfl

@[simp] theorem rightDual_smul_apply {A : Type u} [Ring A]
    (M : LeftModule A) (a : A) (φ : DgaCharacterDual (M : Type u)) (x : M) :
    (MulOpposite.op a • φ) x = φ (a • x) := rfl

/-- The displayed associativity identity for the dual of a right module. -/
theorem leftDual_mul_smul_apply {A : Type u} [Ring A]
    (M : RightModule A) (a b : A) (φ : DgaCharacterDual (M : Type u)) (x : M) :
    ((a * b) • φ) x = (a • (b • φ)) x := by
  change φ (MulOpposite.op (a * b) • x) =
    φ (MulOpposite.op b • (MulOpposite.op a • x))
  rw [MulOpposite.op_mul, smul_smul]

/-! ## Dual maps and the exact dual functors -/

/-- Precomposition with a right-module map, with the induced left-module
structure on character duals. -/
def leftDualMap {A M N : Type u} [Ring A]
    [AddCommGroup M] [AddCommGroup N]
    [Module Aᵐᵒᵖ M] [Module Aᵐᵒᵖ N]
    (f : M →ₗ[Aᵐᵒᵖ] N) :
    DgaCharacterDual N →ₗ[A] DgaCharacterDual M where
  toFun φ := φ.comp f.toAddMonoidHom
  map_add' φ ψ := by
    ext x
    rfl
  map_smul' a φ := by
    ext x
    change (a • φ) (f x) = (a • (φ.comp f.toAddMonoidHom)) x
    change φ (MulOpposite.op a • f x) = φ (f (MulOpposite.op a • x))
    rw [f.map_smul]

/-- Precomposition with a left-module map, with the induced right-module
structure on character duals. -/
def rightDualMap {A M N : Type u} [Ring A]
    [AddCommGroup M] [AddCommGroup N]
    [Module A M] [Module A N]
    (f : M →ₗ[A] N) :
    DgaCharacterDual N →ₗ[Aᵐᵒᵖ] DgaCharacterDual M where
  toFun φ := φ.comp f.toAddMonoidHom
  map_add' φ ψ := by
    ext x
    rfl
  map_smul' a φ := by
    ext x
    change (a • φ) (f x) = (a • (φ.comp f.toAddMonoidHom)) x
    change φ (a.unop • f x) = φ (f (a.unop • x))
    rw [f.map_smul]

/-- The contravariant character-dual functor from right modules to left
modules. -/
def leftDualFunctor {A : Type u} [Ring A] :
    (RightModule A)ᵒᵖ ⥤ LeftModule A where
  obj M := leftDual A M.unop
  map f := ModuleCat.ofHom (leftDualMap f.unop.hom)
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext φ x
    rfl
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext φ x
    rfl

/-- The contravariant character-dual functor from left modules to right
modules. -/
def rightDualFunctor {A : Type u} [Ring A] :
    (LeftModule A)ᵒᵖ ⥤ RightModule A where
  obj M := rightDual A M.unop
  map f := ModuleCat.ofHom (rightDualMap f.unop.hom)
  map_id := by
    intro M
    apply ModuleCat.hom_ext
    ext φ x
    rfl
  map_comp := by
    intro X Y Z f g
    apply ModuleCat.hom_ext
    ext φ x
    rfl

/-- Exactness of the dual functor on right modules. -/
theorem leftDualFunctor_exact {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] :
    IsExact (leftDualFunctor (A := A)) := by
  sorry

/-- Exactness of the dual functor on left modules. -/
theorem rightDualFunctor_exact {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] :
    IsExact (rightDualFunctor (A := A)) := by
  sorry

/-! ## Evaluation -/

/-- Evaluation at an element, as an additive character of the character
dual. -/
def characterEvaluationAt {M : Type u} [AddCommGroup M] (x : M) :
    DgaCharacterDual (DgaCharacterDual M) :=
  { toFun := fun φ => φ x
    map_zero' := by simp
    map_add' := by
      intro φ ψ
      simp }

/-- The evaluation map from a right module to its double character dual. -/
def rightModuleEvaluation {A : Type u} [Ring A] (M : RightModule A) :
    M ⟶ rightDual A (leftDual A M) :=
  ModuleCat.ofHom
    {
      toFun := fun x => characterEvaluationAt x
      map_add' := by
        intro x y
        ext φ
        dsimp [characterEvaluationAt]
        exact φ.map_add x y
      map_smul' := by
        intro a x
        ext φ
        rfl
    }

/-- The evaluation map from a left module to its double character dual. -/
def leftModuleEvaluation {A : Type u} [Ring A] (M : LeftModule A) :
    M ⟶ leftDual A (rightDual A M) :=
  ModuleCat.ofHom
    {
      toFun := fun x => characterEvaluationAt x
      map_add' := by
        intro x y
        ext φ
        dsimp [characterEvaluationAt]
        exact φ.map_add x y
      map_smul' := by
        intro a x
        ext φ
        rfl
    }

/-- The character-dual evaluation map is injective on right modules. -/
theorem rightModuleEvaluation_injective {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (M : RightModule A) :
    Function.Injective (rightModuleEvaluation M) := by
  sorry

/-- The character-dual evaluation map is injective on left modules. -/
theorem leftModuleEvaluation_injective {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (M : LeftModule A) :
    Function.Injective (leftModuleEvaluation M) := by
  sorry

/-! ## The regular dual and its hom description -/

/-- `A^vee` is the dual of the regular left `A`-module, hence a right module. -/
def algebraDual {A : Type u} [Ring A] : RightModule A :=
  rightDual A (ModuleCat.of A A)

/-- The bilinear maps singled out by right `A`-linearity into `A^vee`.

The equality is the source relation between the values on `x ⊗ a` and
`x a ⊗ 1`, with `MulOpposite.op a • x` denoting `x a`. -/
def IsRightDualBalanced {A : Type u} [Ring A] (N : RightModule A)
    (φ : (N : Type u) →+ DgaCharacterDual A) : Prop :=
  ∀ (x : N) (a : A), φ x a = φ (MulOpposite.op a • x) 1

/-- Right-module maps into `A^vee` are exactly the balanced additive maps
displayed in the source. -/
theorem rightModuleHom_iff_balanced {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (N : RightModule A)
    (φ : (N : Type u) →+ DgaCharacterDual A) :
    (∃ f : N ⟶ algebraDual (A := A), f.hom.toAddMonoidHom = φ) ↔
      IsRightDualBalanced N φ := by
  sorry

/- The following additive equivalence is the usable form of the source's
   two displayed Hom equalities. -/
theorem rightModuleHom_to_algebraDual_nonempty {R A : Type u} [CommRing R]
    [Ring A] [Algebra R A] (N : RightModule A) :
    Nonempty
      ((N ⟶ algebraDual (A := A)) ≃+
        DgaCharacterDual (N : Type u)) := by
  sorry

noncomputable def rightModuleHom_to_algebraDual {R A : Type u} [CommRing R]
    [Ring A] [Algebra R A] (N : RightModule A) :
    (N ⟶ algebraDual (A := A)) ≃+ DgaCharacterDual (N : Type u) :=
  Classical.choice
    (rightModuleHom_to_algebraDual_nonempty (R := R) (A := A) N)

/-- The underlying additive tensor-Hom identification used in the source. -/
theorem additive_tensor_hom_equiv_nonempty {N A : Type u}
    [AddCommGroup N] [AddCommGroup A] :
    Nonempty
      ((N →+ DgaCharacterDual A) ≃+
        DgaCharacterDual (TensorProduct ℤ N A)) := by
  sorry

/-! ## Injectivity and embeddings -/

/-- The category of right `A`-modules has enough injectives. -/
theorem rightModuleCategory_has_enough_injectives {R A : Type u}
    [CommRing R] [Ring A] [Algebra R A] :
    EnoughInjectives (RightModule A) := by
  exact ModuleCat.enoughInjectives (Aᵐᵒᵖ)

/-- `A^vee` is an injective right `A`-module. -/
theorem algebraDual_injective {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] :
    Injective (algebraDual (A := A)) := by
  sorry

/-- A direct sum of copies of the regular left `A`-module. -/
abbrev directSumLeftModule (A : Type u) [Ring A] (ι : Type u) : LeftModule A :=
  ModuleCat.of A (DirectSum ι (fun _ : ι => A))

/-- A pointwise product of copies of `A^vee` in the right-module category. -/
abbrev productOfAlgebraDual (A : Type u) [Ring A] (ι : Type u) : RightModule A :=
  ModuleCat.of Aᵐᵒᵖ (ι → (algebraDual (A := A) : Type u))

/-- Every right module admits the source's surjection from a direct sum of
copies of the regular module onto its dual. -/
theorem exists_directSum_left_surjection {R A : Type u} [CommRing R] [Ring A]
    [Algebra R A] (M : RightModule A) :
    ∃ (ι : Type u) (f : directSumLeftModule A ι ⟶ leftDual A M), Epi f := by
  sorry

/-- Every right `A`-module embeds into a product of copies of `A^vee`. -/
theorem exists_mono_to_productOfAlgebraDual {R A : Type u} [CommRing R]
    [Ring A] [Algebra R A] (M : RightModule A) :
    ∃ (ι : Type u) (f : M ⟶ productOfAlgebraDual A ι), Mono f := by
  sorry

end Formalization.Books.Dga.Unit17
