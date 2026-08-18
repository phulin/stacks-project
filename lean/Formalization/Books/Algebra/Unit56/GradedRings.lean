import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.RingHom
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 56: Graded rings

The internally graded ring and module interfaces below are built from Mathlib's
`GradedRing`, `DirectSum.Decomposition`, and `SetLike.GradedSMul`.  The small
wrappers bind the component families to the ambient rings and modules, which
is the form used by the source text.
-/

namespace Formalization.Books.Algebra.Unit56

open DirectSum
open scoped DirectSum Pointwise

universe u v w

noncomputable section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {K M N : Type w}
variable [AddCommGroup K] [AddCommGroup M] [AddCommGroup N]
variable [Module S K] [Module S M] [Module S N]

/-- The degree action of nonnegative ring degrees on integral module degrees. -/
instance natVAddInt : VAdd ℕ ℤ where
  vadd n m := (n : ℤ) + m

/-! ## Graded rings and modules -/

/-- A graded ring in the sense of the source, with nonnegative degrees. -/
structure GradedRingData (S : Type u) [CommRing S] where
  component : ℕ → AddSubgroup S
  graded : GradedRing component

instance (G : GradedRingData S) : GradedRing G.component := G.graded

/-- The degree-zero subring of a graded ring. -/
abbrev degreeZeroSubring (G : GradedRingData S) : Subring S :=
  SetLike.GradeZero.subring G.component

/-- The irrelevant ideal, using Mathlib's canonical homogeneous-ideal API. -/
abbrev irrelevantIdeal (G : GradedRingData S) : Ideal S :=
  (HomogeneousIdeal.irrelevant G.component).toIdeal

/-- Homogeneous elements are Mathlib's `SetLike.IsHomogeneousElem`. -/
abbrev IsHomogeneousElement (G : GradedRingData S) (x : S) : Prop :=
  SetLike.IsHomogeneousElem G.component x

theorem homogeneous_component_mem_irrelevantIdeal
    (G : GradedRingData S) {d : ℕ} :
    0 < d → ∀ x, x ∈ G.component d → x ∈ irrelevantIdeal G := by
  sorry

/-- A graded module is an internally decomposed module with homogeneous scalar action. -/
structure GradedModuleData (G : GradedRingData S) (M : Type w)
    [AddCommGroup M] [Module S M] where
  component : ℤ → AddSubgroup M
  decomposition : DirectSum.Decomposition component
  gradedSMul : SetLike.GradedSMul G.component component

instance (G : GradedRingData S) (𝓜 : GradedModuleData G M) :
    DirectSum.Decomposition 𝓜.component :=
  𝓜.decomposition

instance (G : GradedRingData S) (𝓜 : GradedModuleData G M) :
    SetLike.GradedSMul G.component 𝓜.component :=
  𝓜.gradedSMul

/-- The component family obtained by viewing a nonnegatively graded ring as a module.
Negative components are zero. -/
def ringModuleComponent (G : GradedRingData S) (d : ℤ) : AddSubgroup S :=
  if 0 ≤ d then G.component d.toNat else ⊥

theorem ringModule_decomposition_exists (G : GradedRingData S) :
    Nonempty (DirectSum.Decomposition (ringModuleComponent G)) := by
  sorry

theorem ringModule_gradedSMul (G : GradedRingData S) :
    SetLike.GradedSMul G.component (ringModuleComponent G) := by
  sorry

noncomputable def ringAsGradedModule (G : GradedRingData S) : GradedModuleData G S :=
  { component := ringModuleComponent G
    decomposition := Classical.choice (ringModule_decomposition_exists G)
    gradedSMul := ringModule_gradedSMul G }

@[simp]
theorem ringModuleComponent_of_nonnegative (G : GradedRingData S) {d : ℤ} (hd : 0 ≤ d) :
    ringModuleComponent G d = G.component d.toNat := by
  simp [ringModuleComponent, hd]

@[simp]
theorem ringModuleComponent_of_negative (G : GradedRingData S) {d : ℤ} (hd : d < 0) :
    ringModuleComponent G d = ⊥ := by
  simp [ringModuleComponent, not_le.mpr hd]

/-- The source's homogeneous submodules, using Mathlib's canonical predicate. -/
abbrev IsGradedSubmodule (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N : Submodule S M) : Prop :=
  N.IsHomogeneous 𝓜.component

/-- Homogeneous elements of a graded module. -/
abbrev IsHomogeneousModuleElement (G : GradedRingData S)
    (𝓜 : GradedModuleData G M) (x : M) : Prop :=
  SetLike.IsHomogeneousElem 𝓜.component x

/-- A degree-preserving `S`-linear map between graded modules. -/
def IsGradedLinearMap (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (𝓝 : GradedModuleData G N)
    (f : M →ₗ[S] N) : Prop :=
  ∀ d : ℤ, ∀ x, x ∈ 𝓜.component d → f x ∈ 𝓝.component d

/-- The map induced on homogeneous components by a degree-preserving linear map. -/
def componentAddHom (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (𝓝 : GradedModuleData G N)
    (f : M →ₗ[S] N) (hf : IsGradedLinearMap G 𝓜 𝓝 f) (d : ℤ) :
    𝓜.component d →+ 𝓝.component d where
  toFun x := ⟨f x, hf d x x.property⟩
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp

/-- A short exact sequence of graded modules is short exact in every degree. -/
theorem graded_short_exact_iff_componentwise
    (G : GradedRingData S) (𝓚 : GradedModuleData G K)
    (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (f : K →ₗ[S] M) (g : M →ₗ[S] N)
    (hf : IsGradedLinearMap G 𝓚 𝓜 f) (hg : IsGradedLinearMap G 𝓜 𝓝 g) :
    (Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g) ↔
      ∀ d : ℤ,
        (Function.Injective (componentAddHom G 𝓚 𝓜 f hf d) ∧
          Function.Exact (componentAddHom G 𝓚 𝓜 f hf d)
            (componentAddHom G 𝓜 𝓝 g hg d) ∧
          Function.Surjective (componentAddHom G 𝓜 𝓝 g hg d)) := by
  sorry

/-! ## Twists and graded Hom -/

/-- Existence of the reindexed direct-sum decomposition used by a twist. -/
theorem twist_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n : ℤ) :
    Nonempty (DirectSum.Decomposition (fun d : ℤ => 𝓜.component (n + d))) := by
  sorry

/-- The twist `M(n)`, with `M(n)_d = M_{n+d}`. -/
noncomputable def twist (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n : ℤ) :
    GradedModuleData G M :=
  { component := fun d : ℤ => 𝓜.component (n + d)
    decomposition := Classical.choice (twist_decomposition_exists G 𝓜 n)
    gradedSMul := by
      refine { smul_mem := ?_ }
      intro i j x y hx hy
      have h := 𝓜.gradedSMul.smul_mem hx hy
      change x • y ∈ 𝓜.component ((i : ℤ) + (n + j)) at h
      change x • y ∈ 𝓜.component (n + ((i : ℤ) + j))
      simpa [add_assoc, add_comm, add_left_comm] using h }

@[simp]
theorem twist_component (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n d : ℤ) :
    (twist G 𝓜 n).component d = 𝓜.component (n + d) :=
  rfl

/-- Twisting preserves a degree-preserving linear map on the underlying module. -/
def twistMap (f : M →ₗ[S] N) : M →ₗ[S] N :=
  f

theorem twistMap_isGraded
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (f : M →ₗ[S] N) (hf : IsGradedLinearMap G 𝓜 𝓝 f) (n : ℤ) :
    IsGradedLinearMap G (twist G 𝓜 n) (twist G 𝓝 n) (twistMap f) := by
  intro d x hx
  change x ∈ 𝓜.component (n + d) at hx
  change f x ∈ 𝓝.component (n + d)
  exact hf (n + d) x hx

/-- The twists `S(n)` obtained from the ring viewed as a graded module. -/
abbrev ringTwist (G : GradedRingData S) (n : ℤ) : GradedModuleData G S :=
  twist G (ringAsGradedModule G) n

/-- A degree-preserving linear equivalence of graded modules. -/
structure GradedLinearEquiv (G : GradedRingData S)
    (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) where
  toLinearEquiv : M ≃ₗ[S] N
  map_component' : ∀ d x, x ∈ 𝓜.component d → toLinearEquiv x ∈ 𝓝.component d
  inv_component' : ∀ d y, y ∈ 𝓝.component d → toLinearEquiv.symm y ∈ 𝓜.component d

/-- The homogeneous component of the direct sum of two graded modules. -/
def directSumComponent (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (𝓝 : GradedModuleData G N)
    (d : ℤ) : AddSubgroup (M × N) where
  carrier := {x | x.1 ∈ 𝓜.component d ∧ x.2 ∈ 𝓝.component d}
  zero_mem' := ⟨(𝓜.component d).zero_mem, (𝓝.component d).zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨(𝓜.component d).add_mem hx.1 hy.1,
      (𝓝.component d).add_mem hx.2 hy.2⟩
  neg_mem' := by
    intro x hx
    exact ⟨(𝓜.component d).neg_mem hx.1, (𝓝.component d).neg_mem hx.2⟩

theorem directSum_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Nonempty (DirectSum.Decomposition (directSumComponent G 𝓜 𝓝)) := by
  sorry

theorem directSum_gradedSMul
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    SetLike.GradedSMul G.component (directSumComponent G 𝓜 𝓝) where
  smul_mem := by
    intro i j a b ha hb
    change (a : S) • b.1 ∈ 𝓜.component (i +ᵥ j) ∧
      (a : S) • b.2 ∈ 𝓝.component (i +ᵥ j)
    exact ⟨𝓜.gradedSMul.smul_mem ha hb.1, 𝓝.gradedSMul.smul_mem ha hb.2⟩

noncomputable def directSumGradedModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    GradedModuleData G (M × N) :=
  { component := directSumComponent G 𝓜 𝓝
    decomposition := Classical.choice (directSum_decomposition_exists G 𝓜 𝓝)
    gradedSMul := directSum_gradedSMul G 𝓜 𝓝 }

theorem twist_directSum_isomorphism
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) :
    Nonempty (GradedLinearEquiv G
      (twist G (directSumGradedModule G 𝓜 𝓝) n)
      (directSumGradedModule G (twist G 𝓜 n) (twist G 𝓝 n))) := by
  sorry

/-- Homogeneous tensors of total degree `d`, used for the graded tensor product module. -/
def tensorProductHomogeneousTensors
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (d : ℤ) :
    Set (TensorProduct S M N) :=
  {z | ∃ i j : ℤ, i + j = d ∧ ∃ m, m ∈ 𝓜.component i ∧
    ∃ n, n ∈ 𝓝.component j ∧ TensorProduct.tmul S m n = z}

/-- The graded component of a tensor product is spanned by homogeneous pure tensors. -/
def tensorProductComponent
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (d : ℤ) :
    AddSubgroup (TensorProduct S M N) :=
  (Submodule.span (degreeZeroSubring G)
    (tensorProductHomogeneousTensors G 𝓜 𝓝 d)).toAddSubgroup

theorem tensorProduct_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Nonempty (DirectSum.Decomposition (tensorProductComponent G 𝓜 𝓝)) := by
  sorry

theorem tensorProduct_gradedSMul
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    SetLike.GradedSMul G.component (tensorProductComponent G 𝓜 𝓝) := by
  sorry

noncomputable def tensorProductGradedModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    GradedModuleData G (TensorProduct S M N) :=
  { component := tensorProductComponent G 𝓜 𝓝
    decomposition := Classical.choice (tensorProduct_decomposition_exists G 𝓜 𝓝)
    gradedSMul := tensorProduct_gradedSMul G 𝓜 𝓝 }

theorem twist_tensorProduct_right_isomorphism
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) :
    Nonempty (GradedLinearEquiv G
      (twist G (tensorProductGradedModule G 𝓜 𝓝) n)
      (tensorProductGradedModule G 𝓜 (twist G 𝓝 n))) := by
  sorry

theorem twist_tensorProduct_left_isomorphism
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) :
    Nonempty (GradedLinearEquiv G
      (twist G (tensorProductGradedModule G 𝓜 𝓝) n)
      (tensorProductGradedModule G (twist G 𝓜 n) 𝓝)) := by
  sorry

instance degreeZeroModule
    (G : GradedRingData S) (X : Type w)
    [AddCommGroup X] [Module S X] :
    Module (degreeZeroSubring G) X :=
  Module.compHom X (SubringClass.subtype (degreeZeroSubring G))

/-- The `S_0`-module of degree-zero graded maps. -/
def gradedHomZero
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Submodule (degreeZeroSubring G) (M →ₗ[S] N) where
  carrier := {f | IsGradedLinearMap G 𝓜 𝓝 f}
  zero_mem' := by
    intro d x hx
    exact (𝓝.component d).zero_mem
  add_mem' := by
    intro f g hf hg d x hx
    exact (𝓝.component d).add_mem (hf d x hx) (hg d x hx)
  smul_mem' := by
    intro r f hf d x hx
    have h := 𝓝.gradedSMul.smul_mem r.property (hf d x hx)
    change (r : S) • f x ∈ 𝓝.component d
    change (r : S) • f x ∈ 𝓝.component ((0 : ℤ) + d) at h
    simpa using h

/-- The degree-`n` part of graded Hom is `GrHom_0(M,N(n))`. -/
abbrev gradedHomComponent
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) :
    Type _ := gradedHomZero G 𝓜 (twist G 𝓝 n)

/-- The direct sum of all homogeneous graded maps. -/
abbrev gradedHom
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Type _ := ⨁ n : ℤ, gradedHomComponent G 𝓜 𝓝 n

instance gradedHomDegreeZeroModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Module (degreeZeroSubring G) (gradedHom G 𝓜 𝓝) := inferInstance

theorem gradedHom_gmodule_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Nonempty (DirectSum.Gmodule (fun n : ℕ => G.component n)
      (fun n : ℤ => gradedHomComponent G 𝓜 𝓝 n)) := by
  sorry

noncomputable instance gradedHomGmodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    DirectSum.Gmodule (fun n : ℕ => G.component n)
      (fun n : ℤ => gradedHomComponent G 𝓜 𝓝 n) :=
  Classical.choice (gradedHom_gmodule_exists G 𝓜 𝓝)

/-- The graded Hom is an `S`-module, by transporting the external graded-ring action
along the decomposition equivalence of `S`. -/
noncomputable instance gradedHomModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Module S (gradedHom G 𝓜 𝓝) :=
  Module.compHom _ (DirectSum.decomposeRingEquiv G.component).toRingHom

theorem gradedHomComponent_spec
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) (f : gradedHomComponent G 𝓜 𝓝 n) (d : ℤ) (x : M)
    (hx : x ∈ 𝓜.component d) :
    (f : M →ₗ[S] N) x ∈ 𝓝.component (n + d) := by
  exact f.property d x hx

/-! ## Graded Nakayama -/

theorem graded_nakayama_zero
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Module.Finite S M]
    (hM : irrelevantIdeal G • (⊤ : Submodule S M) = ⊤) :
    (⊤ : Submodule S M) = ⊥ := by
  sorry

theorem graded_nakayama_submodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N N' : Submodule S M)
    (hN : IsGradedSubmodule G 𝓜 N) (hN' : IsGradedSubmodule G 𝓜 N')
    [Module.Finite S N']
    (hM : (⊤ : Submodule S M) = N ⊔ irrelevantIdeal G • N') :
    N = ⊤ := by
  sorry

theorem graded_nakayama_surjective
    (G : GradedRingData S) (𝓝 : GradedModuleData G N) (𝓜 : GradedModuleData G M)
    (f : N →ₗ[S] M) (hf : IsGradedLinearMap G 𝓝 𝓜 f)
    [Module.Finite S M]
    (hquot : Function.Surjective
      ((irrelevantIdeal G • (⊤ : Submodule S M)).mkQ.comp f)) :
    Function.Surjective f := by
  sorry

theorem graded_nakayama_generators
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Module.Finite S M] (n : ℕ) (x : Fin n → M)
    (hx : ∃ d : Fin n → ℤ,
      (∀ i, x i ∈ 𝓜.component (d i)) ∧
        Submodule.span S
          (Set.range (fun i =>
            (irrelevantIdeal G • (⊤ : Submodule S M)).mkQ (x i))) = ⊤) :
    Submodule.span S (Set.range x) = ⊤ := by
  sorry

/-! ## Veronese constructions -/

/-- The restricted graded multiplication on the `d`-th Veronese family. -/
instance veroneseGradedMonoid (G : GradedRingData S) (d : ℕ) :
    SetLike.GradedMonoid (fun n : ℕ => G.component (n * d)) where
  one_mem := by
    simpa using (SetLike.one_mem_graded G.component)
  mul_mem := by
    intro i j x y hx hy
    simpa [Nat.add_mul] using
      (SetLike.mul_mem_graded (A := G.component) hx hy)

/-- The `d`-th Veronese ring, as the external direct sum of the `S_{nd}`. -/
abbrev veroneseRing (G : GradedRingData S) (d : ℕ) : Type _ :=
  ⨁ n : ℕ, G.component (n * d)

/-- The `d`-th Veronese module, as the external direct sum of the `M_{nd}`. -/
abbrev veroneseModule (G : GradedRingData S) (𝓜 : GradedModuleData G M) (d : ℕ) : Type _ :=
  ⨁ n : ℤ, 𝓜.component (n * (d : ℤ))

theorem veroneseModule_is_graded_module
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (d : ℕ) :
    Nonempty (DirectSum.Gmodule
      (fun n : ℕ => G.component (n * d))
      (fun n : ℤ => 𝓜.component (n * (d : ℤ)))) := by
  sorry

noncomputable instance veroneseModuleGmodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (d : ℕ) :
    DirectSum.Gmodule
      (fun n : ℕ => G.component (n * d))
      (fun n : ℤ => 𝓜.component (n * (d : ℤ))) :=
  Classical.choice (veroneseModule_is_graded_module G 𝓜 d)

def veroneseDegreeZeroMap (G : GradedRingData S) (d : ℕ) :
    degreeZeroSubring G → veroneseRing G d :=
  fun x => DirectSum.of _ 0 ⟨(x : S), by
    have hx : (x : S) ∈ G.component 0 := x.property
    simpa using hx⟩

def veroneseDegreeOneMap (G : GradedRingData S) (d : ℕ) :
    G.component d → veroneseRing G d :=
  fun x => DirectSum.of _ 1 ⟨(x : S), by
    rw [Nat.one_mul]
    exact x.property⟩

/-- Generation of a Veronese ring in degree one over its degree-zero ring. -/
def VeroneseGeneratedInDegreeOne (G : GradedRingData S) (d : ℕ) : Prop :=
  Subring.closure
      (Set.range (veroneseDegreeZeroMap G d) ∪
        Set.range (veroneseDegreeOneMap G d)) = (⊤ : Subring (veroneseRing G d))

theorem veronese_generated_in_degree_one
    (G : GradedRingData S)
    (hS : Algebra.FiniteType (degreeZeroSubring G) S) :
    ∃ m : ℕ, 0 < m ∧ ∀ d : ℕ, 0 < d → m ∣ d →
      VeroneseGeneratedInDegreeOne G d := by
  sorry

/-! ## Integral closure -/

/-- A subalgebra is graded when it contains every homogeneous part of each element. -/
def IsGradedSubalgebra (G : GradedRingData S) [Algebra R S] (T : Subalgebra R S) : Prop :=
  ∀ d : ℕ, ∀ x : S, x ∈ T →
    (DirectSum.decompose G.component x d : S) ∈ T

/-- The direct-sum equality for a graded subalgebra, expressed componentwise. -/
def IsDirectSumOfHomogeneousComponents (G : GradedRingData S) [Algebra R S]
    (T : Subalgebra R S) : Prop :=
  ∀ x : S, x ∈ T ↔
    ∀ d : ℕ, (DirectSum.decompose G.component x d : S) ∈ T

theorem isGradedSubalgebra_iff_directSumOfHomogeneousComponents
    (G : GradedRingData S) [Algebra R S] (T : Subalgebra R S) :
    IsGradedSubalgebra G T ↔ IsDirectSumOfHomogeneousComponents G T := by
  sorry

/-- Mathlib's graded ring homomorphism, with the component families supplied by the wrappers. -/
abbrev GradedRingMap (G : GradedRingData R) (H : GradedRingData S) :=
  G.component →+*ᵍ H.component

theorem integralClosure_is_graded
    (G : GradedRingData R) (H : GradedRingData S)
    (f : GradedRingMap G H) :
    let A : Algebra R S := f.toRingHom.toAlgebra
    @IsGradedSubalgebra R S _ _ H A (@integralClosure R S _ _ A) := by
  sorry

theorem integralClosure_is_directSumOfHomogeneousComponents
    (G : GradedRingData R) (H : GradedRingData S)
    (f : GradedRingMap G H) :
    let A : Algebra R S := f.toRingHom.toAlgebra
    @IsDirectSumOfHomogeneousComponents R S _ _ H A (@integralClosure R S _ _ A) := by
  sorry

end

end Formalization.Books.Algebra.Unit56
