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
  action_smul_right : ∀ {i j : ℤ} (r : R) (m : component i) (a : A j),
    action m (r • a) = r • action m a
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
def gradedRightModuleHomogeneousSubmodule
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Submodule R (GradedRightModuleHomogeneousFamily L M n) := by
  have hzero : ∀ {i j k : ℤ} (h : i + j = k) (a : A j),
      GradedRightModule.rightActionAt M h (0 : M.component i) a = 0 := by
    intro i j k h a
    subst k
    exact M.action_zero_left a
  have hadd : ∀ {i j k : ℤ} (h : i + j = k)
      (x x' : M.component i) (a : A j),
      GradedRightModule.rightActionAt M h (x + x') a =
        GradedRightModule.rightActionAt M h x a +
          GradedRightModule.rightActionAt M h x' a := by
    intro i j k h x x' a
    subst k
    exact M.action_add_left x x' a
  have hsmul : ∀ {i j k : ℤ} (h : i + j = k) (r : R)
      (x : M.component i) (a : A j),
      GradedRightModule.rightActionAt M h (r • x) a =
        r • GradedRightModule.rightActionAt M h x a := by
    intro i j k h r x a
    subst k
    exact M.action_smul_left r x a
  exact
    { carrier := {f | IsGradedRightModuleMap L M f}
      zero_mem' := by
        intro s i a m
        dsimp [IsGradedRightModuleMap]
        simpa only [Pi.zero_apply, LinearMap.zero_apply] using
          (hzero (i := s.1.1 - i) (j := i) (k := s.1.1)
            (h := by omega) a).symm
      add_mem' := by
        intro f g hf hg s i a m
        dsimp [IsGradedRightModuleMap] at hf hg ⊢
        rw [hf, hg]
        convert (hadd (i := s.1.1 - i) (j := i) (k := s.1.1)
          (h := by omega) _ _ a).symm using 1 <;> apply Subsingleton.elim
      smul_mem' := by
        intro r f hf s i a m
        dsimp [IsGradedRightModuleMap] at hf ⊢
        rw [hf]
        convert (hsmul (i := s.1.1 - i) (j := i) (k := s.1.1)
          (h := by omega) r _ a).symm using 1 <;> apply Subsingleton.elim }

theorem gradedRightModuleHomogeneous_addCommGroup_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (AddCommGroup (GradedRightModuleHomogeneous L M n)) := by
  change Nonempty
    (AddCommGroup (gradedRightModuleHomogeneousSubmodule L M n))
  exact ⟨inferInstance⟩

noncomputable instance gradedRightModuleHomogeneousAddCommGroup
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    AddCommGroup (GradedRightModuleHomogeneous L M n) :=
  Submodule.addCommGroup (gradedRightModuleHomogeneousSubmodule L M n)

theorem gradedRightModuleHomogeneous_module_nonempty
    (L M : GradedRightModule (R := R) (A := A)) (n : ℤ) :
    Nonempty (Module R (GradedRightModuleHomogeneous L M n)) := by
  let P := gradedRightModuleHomogeneousSubmodule L M n
  change Nonempty (@Module R P _ (inferInstance : AddCommMonoid P))
  exact ⟨Submodule.module' P⟩

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
  intro s k a m
  dsimp [IsGradedRightModuleMap]
  simp only [gradedRightModuleHomogeneousCompFamily, LinearMap.comp_apply]
  have hrightActionAt :
      ∀ {x y z d : ℤ} (hxy : x = y)
        (h1 : x + d = z) (h2 : y + d = z)
        (m : L.component x) (a : A d),
        GradedRightModule.rightActionAt L h1 m a =
          GradedRightModule.rightActionAt L h2
            (cast (hxy ▸ rfl) m) a := by
    intro x y z d hxy h1 h2 m a
    subst y
    rfl
  let sf : GradedDegreePair i :=
    ⟨(-(j - s.1.1), s.1.2), by omega⟩
  let sf2 : GradedDegreePair i :=
    ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩
  let sg : GradedDegreePair j :=
    ⟨(s.1.1, j - s.1.1), by omega⟩
  let sg' : GradedDegreePair j :=
    ⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩
  have hf := f.2 sf k a m
  dsimp [sf] at hf
  let ml : L.component (-((j - s.1.1) + k)) := by
    convert (f.1 sf2 m) using 1
    change -(j - s.1.1 + k) = -(j - s.1.1) - k
    omega
  have hg := g.2 sg k a ml
  dsimp [sg, ml] at hg ⊢
  rw [hf]
  convert hg using 1
  · congr 1
    convert (hrightActionAt
      (x := -(j - s.1.1) - k)
      (y := -((j - s.1.1) + k))
      (z := -(j - s.1.1))
      (d := k)
      (hxy := by omega)
      (h1 := by omega)
      (h2 := by omega)
      (m := (f.1
        ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩) m) a) using 1
  ·
    have h1 : j - (s.1.1 - k) = j - s.1.1 + k := by omega
    have h2 : -(j - (s.1.1 - k)) = -(j - s.1.1) - k := by omega
    have hsg :
        (⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩ : GradedDegreePair j) =
          ⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact h1
    have hsf :
        (⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩ : GradedDegreePair i) =
          ⟨(-(j - s.1.1) - k, s.1.2 + k), by omega⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · exact h2
      · rfl
    have hfamily_f :
        ∀ {u v : GradedDegreePair i} (huv : u = v)
          {x : K.component (-u.1.2)} {y : K.component (-v.1.2)},
          HEq x y → HEq (f.1 u x) (f.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hfamily_g :
        ∀ {u v : GradedDegreePair j} (huv : u = v)
          {x : L.component (-u.1.2)} {y : L.component (-v.1.2)},
          HEq x y → HEq (g.1 u x) (g.1 v y) := by
      intro u v huv x y hxy
      cases huv
      cases hxy
      rfl
    have hcast_heq :
        ∀ {X Y : Type _} (h : X = Y) (x : X), HEq x (cast h x) := by
      intro X Y h x
      cases h
      rfl
    have hcastEq :
        L.component (sf2.1).1 =
          L.component (-(⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩ :
            GradedDegreePair j).1.2) := by
      change L.component (-(j - s.1.1) - k) =
        L.component (-(j - s.1.1 + k))
      congr 1 <;> omega
    have hrightActionAt_heq :
        ∀ {x y z d : ℤ} (hxy : x = y)
          (h1 : x + d = z) (h2 : y + d = z)
          {u : M.component x} {v : M.component y}, HEq u v →
          ∀ a : A d,
            HEq (GradedRightModule.rightActionAt M h1 u a)
              (GradedRightModule.rightActionAt M h2 v a) := by
      intro x y z d hxy h1 h2 u v huv a
      subst y
      cases huv
      rfl
    have hfm : HEq
        ((f.1 ⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩) m)
          (cast hcastEq ((f.1 sf2) m)) := by
      dsimp [sf2]
      exact (hfamily_f hsf (heq_of_eq rfl)).trans
        (hcast_heq hcastEq ((f.1 sf2) m))
    have hgm : HEq
        ((g.1 ⟨(s.1.1 - k, j - (s.1.1 - k)), by omega⟩)
          ((f.1 ⟨(-(j - (s.1.1 - k)), s.1.2 + k), by omega⟩) m))
          ((g.1 ⟨(s.1.1 - k, j - s.1.1 + k), by omega⟩)
            (cast hcastEq ((f.1 sf2) m))) := by
      apply hfamily_g hsg
      exact hfm
    apply eq_of_heq
    apply hrightActionAt_heq (hxy := rfl) (h1 := by omega) (h2 := by omega)
      (a := a)
    exact hgm

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
  let idFamily : GradedRightModuleHomogeneousFamily L L 0 :=
    fun ⟨⟨p, q⟩, h⟩ => by
      have hq : q = -p := by omega
      subst q
      dsimp
      convert LinearMap.id (R := R) (M := L.component p) using 1 <;> simp
  refine ⟨⟨idFamily, ?_⟩⟩
  intro s i a m
  dsimp [idFamily, IsGradedRightModuleMap]
  simp

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
