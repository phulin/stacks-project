import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Module.Projective
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Differential Graded Algebra, Chapter 14: Core interfaces

This file fixes the module conventions used by the three sections of the
chapter.  Lean's module action is a left action, so a right `A`-module is
represented by a module over `Aᵐᵒᵖ`.  A free right module is consequently a
finitely supported family of copies of the regular right module, written as a
finsupp with coefficients in `Aᵐᵒᵖ`.

For graded modules we use Mathlib's external graded-algebra interface.  The
componentwise action below is deliberately small: it supplies exactly the
degree-zero morphisms and shifts used in this chapter, while retaining the
graded module laws instead of treating a graded module as an unstructured
family of types.
-/

noncomputable section

open CategoryTheory
open DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit14

/-! ## Ordinary right modules -/

/-- The free right `A`-module on `I`, expressed as a module over `Aᵐᵒᵖ`.

The opposite-algebra carrier is the canonical scalar-side presentation of a
copy of the regular right `A`-module.
-/
abbrev RightFreeModule (A : Type u) (I : Type v) [Ring A] := I →₀ Aᵐᵒᵖ

/-- Projectivity of a right `A`-module, using Mathlib's canonical definition. -/
abbrev RightModuleProjective (A : Type u) (M : Type v) [Ring A]
    [AddCommGroup M] [Module Aᵐᵒᵖ M] : Prop :=
  Module.Projective Aᵐᵒᵖ M

/-- The category of right `A`-modules in the opposite-algebra convention. -/
abbrev RightModuleCategory (A : Type u) [Ring A] := ModuleCat Aᵐᵒᵖ

/-! ## External graded right modules -/

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-- The homogeneous action associated to a componentwise graded action. -/
def gradedRightAction
    {M : ℤ → Type w}
    (action : ∀ {i j : ℤ}, M i → A j → M (i + j))
    (x : GradedMonoid M) (a : GradedMonoid A) : GradedMonoid M :=
  ⟨x.1 + a.1, action x.2 a.2⟩

/-- A graded right module over the externally graded algebra `A`.

The scalar-linearity fields make the action componentwise `R`-bilinear.  The
last two fields are equations on the sigma types of homogeneous elements, so
that the degree equalities are retained rather than hidden by casts.
-/
structure GradedRightModule where
  component : ℤ → Type w
  addCommGroup : ∀ i, AddCommGroup (component i)
  module : ∀ i, Module R (component i)
  action : ∀ {i j : ℤ}, component i → A j → component (i + j)
  action_zero_left : ∀ {i j : ℤ} (a : A j), action (0 : component i) a = 0
  action_add_left : ∀ {i j : ℤ} (m m' : component i) (a : A j),
    action (m + m') a = action m a + action m' a
  action_zero_right : ∀ {i j : ℤ} (m : component i), action m (0 : A j) = 0
  action_add_right : ∀ {i j : ℤ} (m : component i) (a a' : A j),
    action m (a + a') = action m a + action m a'
  action_smul_left : ∀ {i j : ℤ} (r : R) (m : component i) (a : A j),
    action (r • m) a = r • action m a
  action_smul_right : ∀ {i j : ℤ} (r : R) (m : component i) (a : A j),
    action m (r • a) = r • action m a
  one_action : ∀ (x : GradedMonoid component),
    gradedRightAction action x (1 : GradedMonoid A) = x
  mul_action : ∀ (x : GradedMonoid component) (a b : GradedMonoid A),
    gradedRightAction action (gradedRightAction action x a) b =
      gradedRightAction action x (a * b)

namespace GradedRightModule

variable (M : GradedRightModule (R := R) (A := A))

instance componentAddCommGroup (i : ℤ) : AddCommGroup (M.component i) :=
  M.addCommGroup i

instance componentModule (i : ℤ) : Module R (M.component i) :=
  M.module i

/-- The action on homogeneous elements. -/
def rightAction (x : GradedMonoid M.component) (a : GradedMonoid A) :
    GradedMonoid M.component :=
  gradedRightAction M.action x a

end GradedRightModule

/-- A degree-zero homomorphism of graded right modules. -/
structure GradedRightModuleHom
    (M N : GradedRightModule (R := R) (A := A)) where
  app : ∀ n : ℤ, M.component n →ₗ[R] N.component n
  map_action : ∀ {i j : ℤ} (m : M.component i) (a : A j),
    app (i + j) (M.action m a) = N.action (app i m) a

namespace GradedRightModuleHom

variable {M N P : GradedRightModule (R := R) (A := A)}

/-- The identity degree-zero graded module map. -/
def id (M : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleHom M M where
  app := fun n => LinearMap.id
  map_action := by simp

/-- Composition of degree-zero graded module maps. -/
def comp (f : GradedRightModuleHom M N) (g : GradedRightModuleHom N P) :
    GradedRightModuleHom M P where
  app := fun n => (g.app n).comp (f.app n)
  map_action := by
    intro i j m a
    change g.app (i + j) (f.app (i + j) (M.action m a)) =
      P.action (g.app i (f.app i m)) a
    rw [f.map_action, g.map_action]

omit [DirectSum.GAlgebra R A] in
@[ext]
theorem ext {f g : GradedRightModuleHom M N}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl

end GradedRightModuleHom

instance gradedRightModuleCategory : Category (GradedRightModule (R := R) (A := A)) where
  Hom M N := GradedRightModuleHom M N
  id := GradedRightModuleHom.id
  comp f g := GradedRightModuleHom.comp f g
  id_comp f := by
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro x
    rfl
  comp_id f := by
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro x
    rfl
  assoc f g h := by
    apply GradedRightModuleHom.ext
    intro n
    apply LinearMap.ext
    intro x
    rfl

/-- The category of graded right `A`-modules. -/
abbrev GradedRightModuleCategory := GradedRightModule (R := R) (A := A)

/-- Categorical projectivity in the degree-zero category of graded modules. -/
abbrev GradedProjective (M : GradedRightModule (R := R) (A := A)) : Prop :=
  CategoryTheory.Projective M

/-! ## The regular graded module and shifts -/

/-- Scalar multiplication may be moved across a homogeneous product on the left. -/
theorem graded_mul_smul_left {i j : ℤ} (r : R) (a : A i) (b : A j) :
    GradedMonoid.GMul.mul (r • a) b = r • GradedMonoid.GMul.mul a b := by
  sorry

/-- Scalar multiplication may be moved across a homogeneous product on the right. -/
theorem graded_mul_smul_right {i j : ℤ} (r : R) (a : A i) (b : A j) :
    GradedMonoid.GMul.mul a (r • b) = r • GradedMonoid.GMul.mul a b := by
  sorry

/-- The regular graded right module over an externally graded algebra. -/
def gradedRegularModule : GradedRightModule (R := R) (A := A) where
  component := A
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  action := fun a b => GradedMonoid.GMul.mul a b
  action_zero_left := by
    intro i j a
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul a
  action_add_left := by
    intro i j a b c
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul a b c
  action_zero_right := by
    intro i j a
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero a
  action_add_right := by
    intro i j a b c
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add a b c
  action_smul_left := by
    intro i j r a b
    exact graded_mul_smul_left r a b
  action_smul_right := by
    intro i j r a b
    exact graded_mul_smul_right r a b
  one_action := by
    intro x
    change x * (1 : GradedMonoid A) = x
    exact GradedMonoid.GMonoid.mul_one x
  mul_action := by
    intro x a b
    change (x * a) * b = x * (a * b)
    exact GradedMonoid.GMonoid.mul_assoc x a b

end Formalization.Books.Dga.Unit14
