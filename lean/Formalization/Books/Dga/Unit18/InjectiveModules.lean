import Formalization.Books.Dga.Unit14.GradedProjectiveModules
import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Differential Graded Algebra, Chapter 18: Injective modules over graded algebras

The source uses both left and right graded modules.  Unit14 fixes the
componentwise representation of right graded modules, so this file reuses
that representation and introduces the corresponding left-module interface.
The character dual is the additive character dual from More on Algebra,
applied degree by degree.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit23
open Formalization.Books.Dga.Unit14
open Formalization.Books.MoreAlgebra.Unit55

universe u

namespace Formalization.Books.Dga.Unit18

variable {R : Type u} {A : ℤ → Type u}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-! ## Left graded modules -/

/-- The homogeneous action associated to a left graded-module action. -/
def gradedLeftAction
    {M : ℤ → Type u}
    (action : ∀ {i j : ℤ}, A j → M i → M (j + i))
    (a : GradedMonoid A) (x : GradedMonoid M) : GradedMonoid M :=
  ⟨a.1 + x.1, action a.2 x.2⟩

/-- A graded left module over the externally graded algebra `A`. -/
structure GradedLeftModule where
  component : ℤ → Type u
  addCommGroup : ∀ i, AddCommGroup (component i)
  module : ∀ i, Module R (component i)
  action : ∀ {i j : ℤ}, A j → component i → component (j + i)
  action_zero_left : ∀ {i j : ℤ} (a : A j), action a (0 : component i) = 0
  action_add_left : ∀ {i j : ℤ} (a : A j) (m m' : component i),
    action a (m + m') = action a m + action a m'
  action_zero_right : ∀ {i j : ℤ} (m : component i), action (0 : A j) m = 0
  action_add_right : ∀ {i j : ℤ} (a a' : A j) (m : component i),
    action (a + a') m = action a m + action a' m
  action_smul_left : ∀ {i j : ℤ} (r : R) (a : A j) (m : component i),
    action (r • a) m = r • action a m
  action_smul_right : ∀ {i j : ℤ} (r : R) (a : A j) (m : component i),
    action a (r • m) = r • action a m
  one_action : ∀ (x : GradedMonoid component),
    gradedLeftAction action (1 : GradedMonoid A) x = x
  mul_action : ∀ (a b : GradedMonoid A) (x : GradedMonoid component),
    gradedLeftAction action a (gradedLeftAction action b x) =
      gradedLeftAction action (a * b) x

namespace GradedLeftModule

variable (M : GradedLeftModule (R := R) (A := A))

instance componentAddCommGroup (i : ℤ) : AddCommGroup (M.component i) :=
  M.addCommGroup i

instance componentModule (i : ℤ) : Module R (M.component i) :=
  M.module i

end GradedLeftModule

/-- A degree-zero homomorphism of graded left modules. -/
structure GradedLeftModuleHom
    (M N : GradedLeftModule (R := R) (A := A)) where
  app : ∀ n : ℤ, M.component n →ₗ[R] N.component n
  map_action : ∀ {i j : ℤ} (a : A j) (m : M.component i),
    app (j + i) (M.action a m) = N.action a (app i m)

namespace GradedLeftModuleHom

variable {M N P : GradedLeftModule (R := R) (A := A)}

/-- The identity degree-zero graded left-module map. -/
def id (M : GradedLeftModule (R := R) (A := A)) : GradedLeftModuleHom M M where
  app := fun n => LinearMap.id
  map_action := by simp

/-- Composition of degree-zero graded left-module maps. -/
def comp (f : GradedLeftModuleHom M N) (g : GradedLeftModuleHom N P) :
    GradedLeftModuleHom M P where
  app := fun n => (g.app n).comp (f.app n)
  map_action := by
    intro i j a m
    change g.app (j + i) (f.app (j + i) (M.action a m)) =
      P.action a (g.app i (f.app i m))
    rw [f.map_action, g.map_action]

omit [DirectSum.GAlgebra R A] in
@[ext]
theorem ext {f g : GradedLeftModuleHom M N}
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      have hfg : f = g := funext h
      cases hfg
      rfl

end GradedLeftModuleHom

/-! ## The graded character dual -/

/- The dual components use `CharacterDual R`, the canonical additive
   character dual from More on Algebra.  Thus the displayed direct sum in
   the source is represented by the family of these components. -/

/-! The two homogeneous action formulas are defined before the bundled
   modules so that their degree casts remain visible in the structure bodies. -/

/-- Precomposition with a homogeneous left action, in source coordinates. -/
def gradedLeftDualAction
    (M : GradedLeftModule (R := R) (A := A))
    {n m : ℤ} (f : CharacterDual R (M.component (-n))) (a : A m) :
    CharacterDual R (M.component (-(n + m))) :=
  { toFun := fun x =>
      f (cast (congrArg M.component (by omega : m + (-(n + m)) = -n))
        (M.action a x))
    map_zero' := by sorry
    map_add' := by sorry }

/-- The sign-corrected precomposition action on the dual of a right module. -/
def gradedRightDualAction
    (M : GradedRightModule (R := R) (A := A))
    {n m : ℤ} (a : A n) (f : CharacterDual R (M.component (-m))) :
    CharacterDual R (M.component (-(n + m))) :=
  { toFun := fun x =>
      ((n * m).negOnePow : ℤ) •
        f (cast (congrArg M.component (by omega : (-(n + m)) + n = -m))
          (M.action x a))
    map_zero' := by sorry
    map_add' := by sorry }

/-- The graded character dual of a left graded module, as a right module. -/
def gradedCharacterDualOfLeft (M : GradedLeftModule (R := R) (A := A)) :
    GradedRightModule (R := R) (A := A) where
  component := fun n => CharacterDual R (M.component (-n))
  addCommGroup := fun n => inferInstance
  module := fun n => inferInstance
  action := fun {n m} f a => gradedLeftDualAction M f a
  action_zero_left := by sorry
  action_add_left := by sorry
  action_zero_right := by sorry
  action_add_right := by sorry
  action_smul_left := by sorry
  action_smul_right := by sorry
  one_action := by sorry
  mul_action := by sorry

omit [DirectSum.GAlgebra R A] in
/-- The source formula for the right action on the dual of a left module. -/
theorem gradedLeftDualAction_apply
    (M : GradedLeftModule (R := R) (A := A))
    {n m : ℤ} (f : CharacterDual R (M.component (-n))) (a : A m)
    (x : M.component (-(n + m))) :
    gradedLeftDualAction M f a x =
      f (cast (congrArg M.component (by omega : m + (-(n + m)) = -n))
        (M.action a x)) := rfl

/-- The graded character dual of a right graded module, as a left module. -/
def gradedCharacterDualOfRight (M : GradedRightModule (R := R) (A := A)) :
    GradedLeftModule (R := R) (A := A) where
  component := fun n => CharacterDual R (M.component (-n))
  addCommGroup := fun n => inferInstance
  module := fun n => inferInstance
  action := fun {n m} a f => gradedRightDualAction M a f
  action_zero_left := by sorry
  action_add_left := by sorry
  action_zero_right := by sorry
  action_add_right := by sorry
  action_smul_left := by sorry
  action_smul_right := by sorry
  one_action := by sorry
  mul_action := by sorry

omit [DirectSum.GAlgebra R A] in
/-- The source formula for the left action on the dual of a right module. -/
theorem gradedRightDualAction_apply
    (M : GradedRightModule (R := R) (A := A))
    {m n : ℤ} (a : A n) (f : CharacterDual R (M.component (-m)))
    (x : M.component (-(n + m))) :
    gradedRightDualAction M a f x =
      ((n * m).negOnePow : ℤ) •
        f (cast (congrArg M.component (by omega : (-(n + m)) + n = -m))
          (M.action x a)) := rfl

/-! ## Dual maps and the componentwise exactness assertion -/

/-- The dual map induced by a graded left-module homomorphism. -/
def gradedCharacterDualOfLeftMap
    {M N : GradedLeftModule (R := R) (A := A)}
    (f : GradedLeftModuleHom M N) :
    GradedRightModuleHom (gradedCharacterDualOfLeft N)
      (gradedCharacterDualOfLeft M) where
  app := fun n => characterDualMap (f.app (-n))
  map_action := by sorry

/-- The dual map induced by a graded right-module homomorphism. -/
def gradedCharacterDualOfRightMap
    {M N : GradedRightModule (R := R) (A := A)}
    (f : GradedRightModuleHom M N) :
    GradedLeftModuleHom (gradedCharacterDualOfRight N)
      (gradedCharacterDualOfRight M) where
  app := fun n => characterDualMap (f.app (-n))
  map_action := by sorry

/-- Exactness of the graded character dual, checked componentwise. -/
def GradedCharacterDualExact : Prop :=
  ∀ _ : ℤ, IsExact (characterDualFunctor R)

/-- The componentwise dual functor is exact. -/
theorem gradedCharacterDual_exact : GradedCharacterDualExact (R := R) := by
  intro n
  exact characterDualFunctor_exact R

/-! ## Evaluation -/

/-- Degreewise injectivity of a graded right-module homomorphism. -/
def GradedRightModuleHom.DegreewiseInjective
    {M N : GradedRightModule (R := R) (A := A)}
    (f : GradedRightModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Injective (f.app n)

/-- Degreewise injectivity of a graded left-module homomorphism. -/
def GradedLeftModuleHom.DegreewiseInjective
    {M N : GradedLeftModule (R := R) (A := A)}
    (f : GradedLeftModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Injective (f.app n)

/-- Evaluation from a right graded module to its double dual. -/
def gradedRightEvaluation (M : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleHom M
      (gradedCharacterDualOfLeft (gradedCharacterDualOfRight M)) where
  app := fun n => by
    refine
      { toFun := fun x =>
          (n.negOnePow : ℤ) •
            ((characterDualEvaluation (R := R) (M := M.component (- -n)))
              (cast (congrArg M.component (by omega : n = - -n)) x))
        map_add' := by sorry
        map_smul' := by sorry }
  map_action := by sorry

/-- Evaluation from a left graded module to its double dual. -/
def gradedLeftEvaluation (M : GradedLeftModule (R := R) (A := A)) :
    GradedLeftModuleHom M
      (gradedCharacterDualOfRight (gradedCharacterDualOfLeft M)) where
  app := fun n => by
    refine
      { toFun := fun x =>
          (n.negOnePow : ℤ) •
            ((characterDualEvaluation (R := R) (M := M.component (- -n)))
              (cast (congrArg M.component (by omega : n = - -n)) x))
        map_add' := by sorry
        map_smul' := by sorry }
  map_action := by sorry

/-- The graded evaluation map is injective on right graded modules. -/
theorem gradedRightEvaluation_injective
    (M : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleHom.DegreewiseInjective (gradedRightEvaluation M) := by
  sorry

/-- The graded evaluation map is injective on left graded modules. -/
theorem gradedLeftEvaluation_injective
    (M : GradedLeftModule (R := R) (A := A)) :
    GradedLeftModuleHom.DegreewiseInjective (gradedLeftEvaluation M) := by
  sorry

/-! ## Shifts and the shift-dual isomorphism -/

/-- A graded left-module shift specification, with the Unit14 convention
`M[k]^n = M^(n+k)`. -/
structure GradedLeftShiftSpec
    (M : GradedLeftModule (R := R) (A := A)) (k : ℤ) where
  object : GradedLeftModule (R := R) (A := A)
  component_eq : ∀ n : ℤ, object.component n = M.component (n + k)
  action_eq : ∀ {i j : ℤ} (a : A j) (m : M.component (i + k)),
    HEq
      (object.action a (cast (component_eq i).symm m))
      (M.action a m)

theorem gradedLeftShiftSpec_nonempty
    (M : GradedLeftModule (R := R) (A := A)) (k : ℤ) :
    Nonempty (GradedLeftShiftSpec (R := R) (A := A) M k) := by
  sorry

/-- The graded shift of a left graded module. -/
noncomputable def gradedLeftShift
    (M : GradedLeftModule (R := R) (A := A)) (k : ℤ) :
    GradedLeftModule (R := R) (A := A) :=
  (Classical.choice (gradedLeftShiftSpec_nonempty (R := R) (A := A) M k)).object

theorem gradedLeftShift_component
    (M : GradedLeftModule (R := R) (A := A)) (k n : ℤ) :
    (gradedLeftShift M k).component n = M.component (n + k) :=
  (Classical.choice (gradedLeftShiftSpec_nonempty (R := R) (A := A) M k)).component_eq n

/-- A degree-zero isomorphism of graded right modules. -/
structure GradedRightModuleIso
    (M N : GradedRightModule (R := R) (A := A)) where
  hom : GradedRightModuleHom M N
  inv : GradedRightModuleHom N M
  hom_inv_id : GradedRightModuleHom.comp hom inv = GradedRightModuleHom.id M
  inv_hom_id : GradedRightModuleHom.comp inv hom = GradedRightModuleHom.id N

/-- A degree-zero isomorphism of graded left modules. -/
structure GradedLeftModuleIso
    (M N : GradedLeftModule (R := R) (A := A)) where
  hom : GradedLeftModuleHom M N
  inv : GradedLeftModuleHom N M
  hom_inv_id : GradedLeftModuleHom.comp hom inv = GradedLeftModuleHom.id M
  inv_hom_id : GradedLeftModuleHom.comp inv hom = GradedLeftModuleHom.id N

/-- The canonical shift-dual isomorphism for a left graded module. -/
theorem gradedLeftShift_dual_iso
    (M : GradedLeftModule (R := R) (A := A)) (k : ℤ) :
    Nonempty (GradedRightModuleIso
      (gradedShift (gradedCharacterDualOfLeft M) (-k))
      (gradedCharacterDualOfLeft (gradedLeftShift M k))) := by
  sorry

/-- The canonical shift-dual isomorphism for a right graded module. -/
theorem gradedRightShift_dual_iso
    (M : GradedRightModule (R := R) (A := A)) (k : ℤ) :
    Nonempty (GradedLeftModuleIso
      (gradedLeftShift (gradedCharacterDualOfRight M) (-k))
      (gradedCharacterDualOfRight (gradedShift M k))) := by
  sorry

/-! ## The regular dual and injective embeddings -/

/-- The regular graded left module over `A`. -/
def gradedLeftRegularModule : GradedLeftModule (R := R) (A := A) where
  component := A
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  action := fun a b => GradedMonoid.GMul.mul a b
  action_zero_left := by
    intro i j a
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_zero a
  action_add_left := by
    intro i j a b c
    exact DirectSum.GNonUnitalNonAssocSemiring.mul_add a b c
  action_zero_right := by
    intro i j a
    exact DirectSum.GNonUnitalNonAssocSemiring.zero_mul a
  action_add_right := by
    intro i j a b c
    exact DirectSum.GNonUnitalNonAssocSemiring.add_mul a b c
  action_smul_left := by
    intro i j r a b
    exact graded_mul_smul_left r a b
  action_smul_right := by
    intro i j r a b
    exact graded_mul_smul_right r a b
  one_action := by
    intro x
    change (1 : GradedMonoid A) * x = x
    exact GradedMonoid.GMonoid.one_mul x
  mul_action := by
    intro a b x
    change a * (b * x) = (a * b) * x
    exact (GradedMonoid.GMonoid.mul_assoc a b x).symm

/-- The regular graded dual, an object of the category of right graded
modules. -/
def gradedAlgebraDual : GradedRightModule (R := R) (A := A) :=
  gradedCharacterDualOfLeft (gradedLeftRegularModule (R := R) (A := A))

/- The tensor--Hom description in the source specializes the graded tensor
   product `N ⊗_A A` to `N`; the resulting degree-zero character dual is the
   usable Lean form of both displayed Hom equalities. -/

/-- The displayed Hom identification with the degree-zero character dual. -/
theorem gradedHom_into_algebraDual_equiv
    (N : GradedRightModule (R := R) (A := A)) :
    Nonempty
      (GradedRightModuleHom N (gradedAlgebraDual (R := R) (A := A)) ≃
        CharacterDual R (N.component 0)) := by
  sorry

/-- The regular graded dual is injective. -/
theorem gradedAlgebraDual_injective :
    Injective (gradedAlgebraDual (R := R) (A := A)) := by
  sorry

/-- The shifted regular graded dual. -/
noncomputable def gradedAlgebraDualShift (k : ℤ) :
    GradedRightModule (R := R) (A := A) :=
  gradedShift (gradedAlgebraDual (R := R) (A := A)) k

/-- Every shift of the regular graded dual is injective. -/
theorem gradedAlgebraDualShift_injective (k : ℤ) :
    Injective (gradedAlgebraDualShift (R := R) (A := A) k) := by
  sorry

/-- The category of graded right `A`-modules has enough injectives. -/
theorem graded_right_module_category_has_enough_injectives :
    EnoughInjectives (GradedRightModuleCategory (R := R) (A := A)) := by
  sorry

/-- The componentwise product of a family of graded right modules. -/
def gradedProduct {ι : Type u}
    (F : ι → GradedRightModule (R := R) (A := A)) :
    GradedRightModule (R := R) (A := A) where
  component := fun n => ∀ i, (F i).component n
  addCommGroup := fun n => inferInstance
  module := fun n => inferInstance
  action := fun m a i => (F i).action (m i) a
  action_zero_left := by sorry
  action_add_left := by sorry
  action_zero_right := by sorry
  action_add_right := by sorry
  action_smul_left := by sorry
  action_smul_right := by sorry
  one_action := by sorry
  mul_action := by sorry

/-- A degreewise-surjective graded left-module map. -/
def GradedLeftModuleHom.DegreewiseSurjective
    {M N : GradedLeftModule (R := R) (A := A)}
    (f : GradedLeftModuleHom M N) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.app n)

/-- The shifted-free graded-left module used for homogeneous generators. -/
noncomputable def gradedLeftShiftedFreeAction
    {ι : Type u} (degree : ι → ℤ) {i j : ℤ} (a : A j) :
    DirectSum ι (fun l => A (i + degree l)) →ₗ[R]
      DirectSum ι (fun l => A ((j + i) + degree l)) :=
  by
    classical
    exact DirectSum.toModule R ι
      (DirectSum ι (fun l => A ((j + i) + degree l)))
      (fun l =>
        { toFun := fun b =>
            DirectSum.lof R ι (fun l => A ((j + i) + degree l)) l
              (cast (congrArg A
                (by omega : j + (i + degree l) = (j + i) + degree l))
                (GradedMonoid.GMul.mul a b))
          map_add' := by sorry
          map_smul' := by sorry })

/-- The direct sum of the shifted regular left modules. -/
noncomputable def gradedLeftShiftedFree
    {ι : Type u} (degree : ι → ℤ) : GradedLeftModule (R := R) (A := A) where
  component := fun i => DirectSum ι (fun l => A (i + degree l))
  addCommGroup := fun _ => inferInstance
  module := fun _ => inferInstance
  action := fun {i j} a => gradedLeftShiftedFreeAction (R := R) (A := A) degree a
  action_zero_left := by sorry
  action_add_left := by sorry
  action_zero_right := by sorry
  action_add_right := by sorry
  action_smul_left := by sorry
  action_smul_right := by sorry
  one_action := by sorry
  mul_action := by sorry

omit [DirectSum.GAlgebra R A] in
theorem gradedLeftShiftedFree_component
    {ι : Type u} (degree : ι → ℤ) (n : ℤ) :
    (gradedLeftShiftedFree (R := R) (A := A) degree).component n =
      DirectSum ι (fun i => A (n + degree i)) := rfl

/-- Every graded dual has a shifted-free graded-left presentation.  The
existential form records the homogeneous generators chosen in the source. -/
theorem exists_graded_shifted_free_surjection
    (M : GradedRightModule (R := R) (A := A)) :
    ∃ (ι : Type u) (degree : ι → ℤ)
      (f : GradedLeftModuleHom
        (gradedLeftShiftedFree (R := R) (A := A) degree)
        (gradedCharacterDualOfRight M)),
      GradedLeftModuleHom.DegreewiseSurjective f := by
  sorry

/-- Every graded right module embeds into a componentwise product of shifts of
the regular graded dual. -/
theorem exists_mono_to_gradedProduct_of_dualShifts
    (M : GradedRightModule (R := R) (A := A)) :
    ∃ (ι : Type u) (degree : ι → ℤ)
      (f : M ⟶ gradedProduct (R := R) (A := A)
        (fun i => gradedAlgebraDualShift (R := R) (A := A) (degree i))),
      Mono f := by
  sorry

end Formalization.Books.Dga.Unit18
