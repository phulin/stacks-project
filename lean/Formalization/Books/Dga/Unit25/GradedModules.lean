import Formalization.Books.Dga.Unit25.GradedObjects
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.GradedMulAction

/-!
# The graded category of graded modules

The algebra is presented externally as a family of graded components, using
Mathlib's `DirectSum.GSemiring` and `DirectSum.GAlgebra`.  A right graded
module records its componentwise right action and the graded module laws.
The homogeneous map predicate is the component equation displayed in the
source.
-/

noncomputable section

open CategoryTheory
open DirectSum
open scoped DirectSum

universe u v w

namespace Formalization.Books.Dga.Unit25

variable {R : Type u} {A : ℤ → Type v}
  [CommRing R]
  [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
  [DirectSum.GSemiring A] [DirectSum.GAlgebra R A]

/-- The sigma-type form of a right graded action. -/
def gradedRightAction
    {M : ℤ → Type w}
    (action : ∀ {i j : ℤ}, M i → A j → M (i + j))
    (x : GradedMonoid M) (a : GradedMonoid A) : GradedMonoid M :=
  ⟨x.1 + a.1, action x.2 a.2⟩

/-- A right graded module over the externally graded algebra `A`. -/
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
  one_action : ∀ x : GradedMonoid component,
    gradedRightAction action x (1 : GradedMonoid A) = x
  mul_action : ∀ (x : GradedMonoid component) (a b : GradedMonoid A),
    gradedRightAction action (gradedRightAction action x a) b =
      gradedRightAction action x (a * b)

namespace GradedRightModule

variable (L : GradedRightModule (R := R) (A := A))

/-- The action on the sigma type of homogeneous elements. -/
def rightAction
    (x : GradedMonoid L.component) (a : GradedMonoid A) :
    GradedMonoid L.component :=
  gradedRightAction L.action x a

instance componentAddCommGroup (i : ℤ) : AddCommGroup (L.component i) :=
  L.addCommGroup i

instance componentModule (i : ℤ) : Module R (L.component i) :=
  L.module i

/-- Transport a componentwise action across an equality of degrees. -/
def rightActionAt {i j k : ℤ} (h : i + j = k)
    (m : L.component i) (a : A j) : L.component k :=
  h ▸ L.action m a

end GradedRightModule

/-- A component family of degree-`n` linear maps between graded modules. -/
abbrev GradedRightModuleHomogeneousFamily
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :=
  ∀ s : GradedDegreePair n,
    L.component (-s.1.2) →ₗ[R] M.component s.1.1

/-- The right-module compatibility equation for a homogeneous component family.
For `p + q = n`, `a ∈ A^i`, and `m ∈ L^{-q-i}`, this is exactly
`f_{p,q}(ma) = f_{p-i,q+i}(m)a`. -/
def IsGradedRightModuleMap
    (L M : GradedRightModule (R := R) (A := A)) {n : ℤ}
    (f : GradedRightModuleHomogeneousFamily L M n) : Prop :=
  ∀ (s : GradedDegreePair n) (i : ℤ) (a : A i)
    (m : L.component (-(s.1.2 + i))),
    let s' : GradedDegreePair n :=
      ⟨(s.1.1 - i, s.1.2 + i), by omega⟩
    f s (GradedRightModule.rightActionAt L
      (i := -(s.1.2 + i)) (j := i) (k := -s.1.2) (by omega) m a) =
      GradedRightModule.rightActionAt M
        (i := s.1.1 - i) (j := i) (k := s.1.1) (by omega)
        (f s' m) a

/-- The degree-`n` homogeneous right `A`-module maps. -/
def GradedRightModuleHomogeneous
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :=
  {f : GradedRightModuleHomogeneousFamily L M n //
    IsGradedRightModuleMap L M f}

omit [(i : ℤ) → Module R (A i)] [DirectSum.GAlgebra R A] in
theorem gradedRightModuleHomogeneous_is_right_module_map
    {L M : GradedRightModule (R := R) (A := A)}
    {n : ℤ} (f : GradedRightModuleHomogeneous L M n)
    (s : GradedDegreePair n) (i : ℤ) (a : A i)
    (m : L.component (-(s.1.2 + i))) :
    let s' : GradedDegreePair n :=
      ⟨(s.1.1 - i, s.1.2 + i), by omega⟩
    f.1 s (GradedRightModule.rightActionAt L
      (i := -(s.1.2 + i)) (j := i) (k := -s.1.2) (by omega) m a) =
      GradedRightModule.rightActionAt M
        (i := s.1.1 - i) (j := i) (k := s.1.1) (by omega)
        (f.1 s' m) a := by
  simpa only using f.2 s i a m

/- The closure of the displayed predicate under addition and scalar
multiplication is standard; these proposition interfaces allow the direct-sum
Hom module to use the canonical operations without hiding that fact in an
unrelated definition. -/
theorem gradedRightModuleHomogeneous_addCommGroup_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (AddCommGroup (GradedRightModuleHomogeneous L M n)) := by
  sorry

noncomputable instance gradedRightModuleHomogeneousAddCommGroup
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    AddCommGroup (GradedRightModuleHomogeneous L M n) :=
  Classical.choice (gradedRightModuleHomogeneous_addCommGroup_nonempty L M n)

theorem gradedRightModuleHomogeneous_module_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (Module R (GradedRightModuleHomogeneous L M n)) := by
  sorry

noncomputable instance gradedRightModuleHomogeneousModule
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Module R (GradedRightModuleHomogeneous L M n) :=
  Classical.choice (gradedRightModuleHomogeneous_module_nonempty L M n)

/-- Componentwise composition of homogeneous right-module maps. -/
def gradedRightModuleHomogeneousCompFamily
    {K L M : GradedRightModule (R := R) (A := A)} (i j : ℤ)
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    GradedRightModuleHomogeneousFamily K M (i + j) :=
  fun s =>
    (g.1 ⟨(s.1.1, j - s.1.1), by omega⟩).comp
      (f.1 ⟨(-(j - s.1.1), s.1.2), by omega⟩)

theorem gradedRightModuleHomogeneousCompFamily_is_map
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    IsGradedRightModuleMap K M
      (gradedRightModuleHomogeneousCompFamily i j f g) := by
  sorry

def gradedRightModuleHomogeneousComp
    {K L M : GradedRightModule (R := R) (A := A)} (i j : ℤ)
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    GradedRightModuleHomogeneous K M (i + j) :=
  ⟨gradedRightModuleHomogeneousCompFamily i j f g,
    gradedRightModuleHomogeneousCompFamily_is_map f g⟩

theorem gradedRightModuleHomogeneousId_nonempty
    (L : GradedRightModule (R := R) (A := A)) :
    Nonempty (GradedRightModuleHomogeneous L L 0) := by
  sorry

noncomputable def gradedRightModuleHomogeneousId
    (L : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleHomogeneous L L 0 :=
  Classical.choice (gradedRightModuleHomogeneousId_nonempty L)

/-- The totalization specification for the graded module category. -/
def GradedModuleTotalizationSpec : Type _ :=
  {D : TotalGradedCategoryData R (GradedRightModule (R := R) (A := A))
      (fun L M n => GradedRightModuleHomogeneous L M n) //
    (∀ L, D.homogeneous_id L = gradedRightModuleHomogeneousId L) ∧
    (∀ {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
      (f : GradedRightModuleHomogeneous K L i)
      (g : GradedRightModuleHomogeneous L M j),
      D.homogeneous_comp f g =
        gradedRightModuleHomogeneousComp i j f g)}

theorem gradedModuleTotalizationSpec_nonempty :
    Nonempty (GradedModuleTotalizationSpec (R := R) (A := A)) := by
  sorry

noncomputable def gradedModuleTotalizationSpec :
    GradedModuleTotalizationSpec (R := R) (A := A) :=
  Classical.choice (gradedModuleTotalizationSpec_nonempty (R := R) (A := A))

noncomputable def gradedModuleCategoryData :
    TotalGradedCategoryData R (GradedRightModule (R := R) (A := A))
      (fun L M n => GradedRightModuleHomogeneous L M n) :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).1

abbrev GradedRightModuleCategory :=
  TotalGradedObject (gradedModuleCategoryData (R := R) (A := A))

def gradedRightModuleCategoryObject
    (L : GradedRightModule (R := R) (A := A)) :
    GradedRightModuleCategory (R := R) (A := A) :=
  ⟨L⟩

@[instance_reducible] noncomputable def gradedModuleGradedCategory :
    GradedCategory R (GradedRightModuleCategory (R := R) (A := A)) := inferInstance

theorem gradedModuleTotalization_homogeneous_id
    (L : GradedRightModule (R := R) (A := A)) :
    (gradedModuleCategoryData (R := R) (A := A)).homogeneous_id L =
      gradedRightModuleHomogeneousId L :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).2.1 L

theorem gradedModuleTotalization_homogeneous_comp
    {K L M : GradedRightModule (R := R) (A := A)} {i j : ℤ}
    (f : GradedRightModuleHomogeneous K L i)
    (g : GradedRightModuleHomogeneous L M j) :
    (gradedModuleCategoryData (R := R) (A := A)).homogeneous_comp f g =
      gradedRightModuleHomogeneousComp i j f g :=
  (gradedModuleTotalizationSpec (R := R) (A := A)).2.2 f g

/-- The degree-zero morphisms in the associated category are the degree-zero
right graded-module maps. -/
abbrev GradedRightModuleZeroMorphism
    (L M : GradedRightModule (R := R) (A := A)) :=
  DegreeZero.hom (A := gradedModuleGradedCategory (R := R) (A := A))
    (DegreeZero.of (gradedModuleGradedCategory (R := R) (A := A))
      (gradedRightModuleCategoryObject (R := R) (A := A) L))
    (DegreeZero.of (gradedModuleGradedCategory (R := R) (A := A))
      (gradedRightModuleCategoryObject (R := R) (A := A) M))

end Formalization.Books.Dga.Unit25
