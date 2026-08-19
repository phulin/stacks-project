import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.GradedAlgebra.FiniteType
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
  intro hd x hx
  exact HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := G.component) hd hx

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
  let emb : ∀ n : ℕ, G.component n →+ ringModuleComponent G (n : ℤ) :=
    fun n =>
      { toFun := fun x => ⟨x, by simp [ringModuleComponent]⟩
        map_zero' := by
          ext
          rfl
        map_add' := by
          intro x y
          ext
          rfl }
  let φ : ∀ n : ℕ, G.component n →+ (⨁ d : ℤ, ringModuleComponent G d) :=
    fun n => (DirectSum.of (fun d : ℤ => ringModuleComponent G d) (n : ℤ)).comp (emb n)
  let decompose : S →+ (⨁ d : ℤ, ringModuleComponent G d) :=
    (DirectSum.toAddMonoid φ).comp
      (DirectSum.decomposeAddEquiv G.component).toAddMonoidHom
  refine ⟨{ decompose' := decompose, left_inv := ?_, right_inv := ?_ }⟩
  · have hcoe :
        (DirectSum.coeAddMonoidHom (ringModuleComponent G)).comp (DirectSum.toAddMonoid φ) =
          DirectSum.coeAddMonoidHom G.component := by
      apply DirectSum.addHom_ext
      intro n x
      change
        DirectSum.coeAddMonoidHom (ringModuleComponent G)
            ((DirectSum.toAddMonoid φ)
              (DirectSum.of (fun n : ℕ => G.component n) n x)) =
          DirectSum.coeAddMonoidHom G.component
            (DirectSum.of (fun n : ℕ => G.component n) n x)
      rw [DirectSum.toAddMonoid_of, DirectSum.coeAddMonoidHom_of]
      change DirectSum.coeAddMonoidHom (ringModuleComponent G) (φ n x) = (x : S)
      change
        DirectSum.coeAddMonoidHom (ringModuleComponent G)
            ((DirectSum.of (fun d : ℤ => ringModuleComponent G d) (n : ℤ)).comp
              (emb n) x) = (x : S)
      rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      rfl
    intro x
    change
      ((DirectSum.coeAddMonoidHom (ringModuleComponent G)).comp
        (DirectSum.toAddMonoid φ))
        ((DirectSum.decomposeAddEquiv G.component).toAddMonoidHom x) = x
    rw [hcoe]
    exact (DirectSum.decomposeAddEquiv G.component).left_inv x
  · have hright :
        decompose.comp (DirectSum.coeAddMonoidHom (ringModuleComponent G)) =
          AddMonoidHom.id _ := by
      apply DirectSum.addHom_ext
      intro d x
      by_cases hd : 0 ≤ d
      · have hx : (x : S) ∈ G.component d.toNat := by
          simpa [ringModuleComponent, hd] using x.property
        let y : G.component d.toNat := ⟨x, hx⟩
        have hdec :
            DirectSum.decompose G.component (x : S) =
              DirectSum.of (fun n : ℕ => G.component n) d.toNat y := by
          exact DirectSum.decompose_coe G.component y
        have hdcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd
        have hcomp :
            ringModuleComponent G (d.toNat : ℤ) = ringModuleComponent G d :=
          congrArg (ringModuleComponent G) hdcast
        have coe_transport :
            ∀ {i j : ℤ} (h : i = j) (z : ringModuleComponent G i),
              ((h ▸ z : ringModuleComponent G j) : S) = (z : S) := by
          intro i j h z
          cases h
          rfl
        change
          (DirectSum.toAddMonoid φ)
              ((DirectSum.decomposeAddEquiv G.component).toAddMonoidHom
                ((DirectSum.coeAddMonoidHom (ringModuleComponent G))
                  (DirectSum.of (fun i : ℤ => ringModuleComponent G i) d x))) =
            (DirectSum.of (fun i : ℤ => ringModuleComponent G i) d x)
        simp only [DirectSum.coeAddMonoidHom_of]
        change
          (DirectSum.toAddMonoid φ) (DirectSum.decompose G.component (x : S)) =
            (DirectSum.of (fun i : ℤ => ringModuleComponent G i) d x)
        rw [hdec]
        simp only [DirectSum.toAddMonoid_of]
        change
          DirectSum.of (fun i : ℤ => ringModuleComponent G i) (d.toNat : ℤ)
              (emb d.toNat y) =
            DirectSum.of (fun i : ℤ => ringModuleComponent G i) d x
        apply DirectSum.ext
        intro i
        by_cases hi : i = d
        · subst i
          rw [DirectSum.of_eq_same]
          rw [DirectSum.of_apply]
          simp only [dif_pos hdcast]
          apply Subtype.ext
          exact (coe_transport hdcast (emb d.toNat y)).trans (by rfl)
        · have hi' : i ≠ (d.toNat : ℤ) := by
            intro hi'
            exact hi (hi'.trans hdcast)
          rw [DirectSum.of_eq_of_ne _ _ _ hi',
            DirectSum.of_eq_of_ne _ _ _ hi]
      · have hx : (x : S) = 0 := by
          simpa [ringModuleComponent, hd] using x.property
        have hx' : x = 0 := Subtype.ext hx
        rw [hx']
        simp [decompose]
    intro x
    simpa only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] using
      DFunLike.congr_fun hright x

theorem ringModule_gradedSMul (G : GradedRingData S) :
    SetLike.GradedSMul G.component (ringModuleComponent G) := by
  refine { smul_mem := ?_ }
  intro i j x y hx hy
  change x • y ∈ ringModuleComponent G ((i : ℤ) + j)
  by_cases hj : 0 ≤ j
  · have hy' : (y : S) ∈ G.component j.toNat := by
      simpa [ringModuleComponent, hj] using hy
    have h := G.graded.mul_mem hx hy'
    have hsum : 0 ≤ (i : ℤ) + j := add_nonneg (Int.natCast_nonneg i) hj
    have hjcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj
    have hcast : ((i + j.toNat : ℕ) : ℤ) = (i : ℤ) + j := by
      simp [hjcast]
    have hto : ((i : ℤ) + j).toNat = i + j.toNat := by
      apply Int.ofNat_inj.mp
      calc
        (((i : ℤ) + j).toNat : ℤ) = (i : ℤ) + j := Int.toNat_of_nonneg hsum
        _ = ((i + j.toNat : ℕ) : ℤ) := hcast.symm
    simpa [ringModuleComponent, hsum, hto, smul_eq_mul] using h
  · have hy0 : (y : S) = 0 := by
      simpa [ringModuleComponent, hj] using hy
    rw [hy0, smul_zero]
    exact (ringModuleComponent G ((i : ℤ) + j)).zero_mem

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
  classical
  have hmapf (x : K) :
      DirectSum.coeAddMonoidHom 𝓜.component
          (DirectSum.map (fun d => componentAddHom G 𝓚 𝓜 f hf d)
            (DirectSum.decompose 𝓚.component x)) = f x := by
    induction x using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓚.component) with
    | zero => simp
    | homogeneous x =>
        simp [componentAddHom]
    | add x y hx hy =>
        simp [DirectSum.decompose_add, hx, hy]
  have hmapg (x : M) :
      DirectSum.coeAddMonoidHom 𝓝.component
          (DirectSum.map (fun d => componentAddHom G 𝓜 𝓝 g hg d)
            (DirectSum.decompose 𝓜.component x)) = g x := by
    induction x using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓜.component) with
    | zero => simp
    | homogeneous x =>
        simp [componentAddHom]
    | add x y hx hy =>
        simp [DirectSum.decompose_add, hx, hy]
  have hcomponent_f (x : K) (d : ℤ) :
      componentAddHom G 𝓚 𝓜 f hf d (DirectSum.decompose 𝓚.component x d) =
        DirectSum.decompose 𝓜.component (f x) d := by
    have h : DirectSum.decompose 𝓜.component (f x) =
        DirectSum.map (fun d => componentAddHom G 𝓚 𝓜 f hf d)
          (DirectSum.decompose 𝓚.component x) := by
      rw [← hmapf x]
      exact (DirectSum.decompose 𝓜.component).apply_symm_apply _
    simpa using congrArg (fun z => z d) h.symm
  have hcomponent_g (x : M) (d : ℤ) :
      componentAddHom G 𝓜 𝓝 g hg d (DirectSum.decompose 𝓜.component x d) =
        DirectSum.decompose 𝓝.component (g x) d := by
    have h : DirectSum.decompose 𝓝.component (g x) =
        DirectSum.map (fun d => componentAddHom G 𝓜 𝓝 g hg d)
          (DirectSum.decompose 𝓜.component x) := by
      rw [← hmapg x]
      exact (DirectSum.decompose 𝓝.component).apply_symm_apply _
    simpa using congrArg (fun z => z d) h.symm
  constructor
  · rintro ⟨hinj, hexact, hsurj⟩ d
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      apply Subtype.ext
      exact hinj (congrArg Subtype.val hxy)
    · apply Function.Exact.of_comp_of_mem_range
      · funext x
        change componentAddHom G 𝓜 𝓝 g hg d
            (componentAddHom G 𝓚 𝓜 f hf d x) = 0
        apply Subtype.ext
        change g (f (x : K)) = 0
        exact hexact.apply_apply_eq_zero (x : K)
      · intro x hx
        rcases (hexact (x : M)).mp (congrArg Subtype.val hx) with ⟨y, hy⟩
        refine ⟨DirectSum.decompose 𝓚.component y d, ?_⟩
        apply Subtype.ext
        calc
          f (DirectSum.decompose 𝓚.component y d) =
              (DirectSum.decompose 𝓜.component (f y) d : M) :=
            congrArg Subtype.val (hcomponent_f y d)
          _ = x := by
            rw [hy]
            exact DirectSum.decompose_of_mem_same 𝓜.component x.property
    · intro y
      rcases hsurj (y : N) with ⟨x, hx⟩
      refine ⟨DirectSum.decompose 𝓜.component x d, ?_⟩
      apply Subtype.ext
      rw [hcomponent_g x d, hx]
      exact DirectSum.decompose_of_mem_same 𝓝.component y.property
  · intro h
    have hcomp := fun d => h d
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      apply (DirectSum.decompose 𝓚.component).injective
      apply DirectSum.ext
      intro d
      apply (hcomp d).1
      apply Subtype.ext
      rw [hcomponent_f x d, hcomponent_f y d, hxy]
    · apply LinearMap.exact_of_comp_of_mem_range
      · apply LinearMap.ext
        intro x
        induction x using DirectSum.Decomposition.inductionOn
          (ℳ := 𝓚.component) with
        | zero => simp
        | @homogeneous d x =>
            exact congrArg Subtype.val
              ((hcomp d).2.1.apply_apply_eq_zero x)
        | add x y hx hy =>
            simpa using congrArg₂ (· + ·) hx hy
      · intro x hx
        have hxcomp : ∀ d, (DirectSum.decompose 𝓜.component x d : M) ∈
            LinearMap.range f := by
          intro d
          have hzero :
              componentAddHom G 𝓜 𝓝 g hg d (DirectSum.decompose 𝓜.component x d) = 0 := by
            rw [hcomponent_g x d, hx]
            simp
          rcases ((hcomp d).2.1 (DirectSum.decompose 𝓜.component x d)).mp hzero with
            ⟨y, hy⟩
          exact ⟨y, congrArg Subtype.val hy⟩
        rw [← DirectSum.sum_support_decompose 𝓜.component x]
        exact (LinearMap.range f).sum_mem (fun d _ => hxcomp d)
    · intro y
      have hycomp : ∀ d, (DirectSum.decompose 𝓝.component y d : N) ∈
          LinearMap.range g := by
        intro d
        rcases (hcomp d).2.2 (DirectSum.decompose 𝓝.component y d) with ⟨x, hx⟩
        exact ⟨x, congrArg Subtype.val hx⟩
      rw [← DirectSum.sum_support_decompose 𝓝.component y]
      exact (LinearMap.range g).sum_mem (fun d _ => hycomp d)

/-! ## Twists and graded Hom -/

/-- Existence of the reindexed direct-sum decomposition used by a twist. -/
theorem twist_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n : ℤ) :
    Nonempty (DirectSum.Decomposition (fun d : ℤ => 𝓜.component (n + d))) := by
  classical
  let e : ℤ ≃ ℤ :=
    { toFun := fun d => d - n
      invFun := fun d => n + d
      left_inv := by
        intro d
        simp [sub_eq_add_neg]
      right_inv := by
        intro d
        simp [sub_eq_add_neg] }
  have he : (fun d : ℤ => 𝓜.component (e.symm d)) =
      (fun d : ℤ => 𝓜.component (n + d)) := by
    funext d
    simp [e]
  let decompose0 : M →+ (⨁ d : ℤ, 𝓜.component (e.symm d)) :=
    (DirectSum.equivCongrLeft e).toAddMonoidHom.comp
      (DirectSum.decomposeAddEquiv 𝓜.component).toAddMonoidHom
  have hdecompose0 :
      Nonempty (DirectSum.Decomposition (fun d : ℤ => 𝓜.component (e.symm d))) := by
    refine ⟨{ decompose' := decompose0, left_inv := ?_, right_inv := ?_ }⟩
    · intro x
      induction x using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
      | zero => simp [decompose0]
      | @homogeneous i x =>
          change DirectSum.coeAddMonoidHom
              (fun d => 𝓜.component (e.symm d))
              ((DirectSum.equivCongrLeft (β := fun i => 𝓜.component i) e)
                (DirectSum.decompose 𝓜.component (x : M))) =
            (x : M)
          rw [DirectSum.decompose_coe]
          let x' : 𝓜.component (e.symm (e i)) :=
            ⟨x, by simp⟩
          have hinput : DirectSum.of (fun i => 𝓜.component i) i x =
              DirectSum.of (fun i => 𝓜.component i) (e.symm (e i)) x' := by
            apply DirectSum.ext
            intro j
            by_cases hji : i = j
            · subst j
              rw [DirectSum.of_eq_same]
              rw [DirectSum.of_apply]
              simp only [dif_pos (e.symm_apply_apply i)]
              apply Subtype.ext
              have h : e.symm (e i) = i := e.symm_apply_apply i
              have htransport :
                  ∀ {C : ℤ → Type w} {a b : ℤ} (hab : a = b) (z : C a)
                    (val : ∀ d, C d → M),
                    val b (hab ▸ z) = val a z := by
                intro C a b hab z val
                cases hab
                simp
              exact (htransport (C := fun d => 𝓜.component d) h x'
                (fun _ z => (z : M))).symm
            · have hji' : e.symm (e i) ≠ j := by
                intro h
                apply hji
                calc
                  i = e.symm (e i) := (e.symm_apply_apply i).symm
                  _ = j := h
              rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji),
                DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji')]
          rw [hinput, DirectSum.equivCongrLeft_of]
          simp [x']
      | add x y hx hy =>
          rw [map_add, map_add, hx, hy]
    · intro x
      induction x using DirectSum.induction_on with
      | zero => simp [decompose0]
      | add x y hx hy =>
          rw [map_add, map_add, hx, hy]
      | of i x =>
          simp [decompose0]
  exact he ▸ hdecompose0

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
  classical
  let inl : ∀ d : ℤ, 𝓜.component d →+
      directSumComponent G 𝓜 𝓝 d := fun d =>
    { toFun := fun x => ⟨(x, 0), ⟨x.property, (𝓝.component d).zero_mem⟩⟩
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp }
  let inr : ∀ d : ℤ, 𝓝.component d →+
      directSumComponent G 𝓜 𝓝 d := fun d =>
    { toFun := fun y => ⟨(0, y), ⟨(𝓜.component d).zero_mem, y.property⟩⟩
      map_zero' := by ext <;> simp
      map_add' := by intro x y; ext <;> simp }
  let left : (⨁ d : ℤ, 𝓜.component d) →+
      (⨁ d : ℤ, directSumComponent G 𝓜 𝓝 d) := DirectSum.map inl
  let right : (⨁ d : ℤ, 𝓝.component d) →+
      (⨁ d : ℤ, directSumComponent G 𝓜 𝓝 d) := DirectSum.map inr
  let decompose : (M × N) →+
      (⨁ d : ℤ, directSumComponent G 𝓜 𝓝 d) :=
    { toFun := fun x => left (DirectSum.decompose 𝓜.component x.1) +
          right (DirectSum.decompose 𝓝.component x.2)
      map_zero' := by
        simp [left, right]
      map_add' := by
        intro x y
        change left (DirectSum.decompose 𝓜.component (x.1 + y.1)) +
            right (DirectSum.decompose 𝓝.component (x.2 + y.2)) =
          (left (DirectSum.decompose 𝓜.component x.1) +
            right (DirectSum.decompose 𝓝.component x.2)) +
          (left (DirectSum.decompose 𝓜.component y.1) +
            right (DirectSum.decompose 𝓝.component y.2))
        simp only [DirectSum.decompose_add, map_add]
        ac_rfl }
  have hleft (x : M) :
      DirectSum.coeAddMonoidHom (directSumComponent G 𝓜 𝓝)
          (left (DirectSum.decompose 𝓜.component x)) = (x, 0) := by
    induction x using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓜.component) with
    | zero => simp [left]; rfl
    | homogeneous x =>
        simp [left, inl]
    | add x y hx hy =>
        simp [left, hx, hy]
  have hright (y : N) :
      DirectSum.coeAddMonoidHom (directSumComponent G 𝓜 𝓝)
          (right (DirectSum.decompose 𝓝.component y)) = (0, y) := by
    induction y using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓝.component) with
    | zero => simp [right]; rfl
    | homogeneous y =>
        simp [right, inr]
    | add x y hx hy =>
        simp [right, hx, hy]
  refine ⟨{ decompose' := decompose, left_inv := ?_, right_inv := ?_ }⟩
  · intro x
    change DirectSum.coeAddMonoidHom (directSumComponent G 𝓜 𝓝)
      (left (DirectSum.decompose 𝓜.component x.1) +
        right (DirectSum.decompose 𝓝.component x.2)) = x
    rw [map_add, hleft x.1, hright x.2]
    ext <;> simp
  · intro x
    induction x using DirectSum.induction_on with
    | zero => simp [decompose, left, right]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
      | of d x =>
        rcases x with ⟨⟨x, y⟩, ⟨hx, hy⟩⟩
        have hx' : x ∈ 𝓜.component d := by simpa using hx
        have hy' : y ∈ 𝓝.component d := by simpa using hy
        simp only [decompose, AddMonoidHom.coe_mk, DirectSum.coeAddMonoidHom_of]
        change left (DirectSum.decompose 𝓜.component x) +
            right (DirectSum.decompose 𝓝.component y) =
          DirectSum.of (fun i => directSumComponent G 𝓜 𝓝 i) d
            ⟨(x, y), ⟨hx', hy'⟩⟩
        rw [DirectSum.decompose_of_mem 𝓜.component hx',
          DirectSum.decompose_of_mem 𝓝.component hy']
        simp [left, right, inl, inr]
        rw [← (DirectSum.of (fun i => directSumComponent G 𝓜 𝓝 i) d).map_add]
        congr 1
        ext <;> simp

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
  refine ⟨{ toLinearEquiv := LinearEquiv.refl S (M × N), map_component' := ?_, inv_component' := ?_ }⟩
  · intro d x hx
    change x ∈ directSumComponent G (twist G 𝓜 n) (twist G 𝓝 n) d
    simpa [twist, directSumGradedModule, directSumComponent] using hx
  · intro d x hx
    change x ∈ (twist G (directSumGradedModule G 𝓜 𝓝) n).component d
    simpa [twist, directSumGradedModule, directSumComponent] using hx

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

private lemma tensorProduct_smul_of_tmul
    (G : GradedRingData S) {P : Type*} [AddCommGroup P]
    [Module (degreeZeroSubring G) P]
    (F : TensorProduct S M N →+ P) (c : degreeZeroSubring G)
    (h : ∀ x : M, ∀ y : N,
      F ((c : S) • (x ⊗ₜ[S] y)) = c • F (x ⊗ₜ[S] y))
    (x : TensorProduct S M N) :
    F ((c : S) • x) = c • F x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [TensorProduct.smul_zero, F.map_zero, smul_zero]
  | @tmul x y => exact h x y
  | @add x y hx hy =>
      have hmap : F (x + y) = F x + F y := F.map_add x y
      have hscalar : c • F x + c • F y = c • F (x + y) :=
        (smul_add c (F x) (F y)).symm.trans
          (congrArg (fun z => c • z) hmap.symm)
      calc
        F ((c : S) • (x + y)) = F ((c : S) • x + (c : S) • y) :=
          congrArg F (smul_add (c : S) x y)
        _ = F ((c : S) • x) + F ((c : S) • y) := F.map_add _ _
        _ = c • F x + c • F y := congrArg₂ (· + ·) hx hy
        _ = c • F (x + y) := hscalar

private lemma tensorProduct_addHom_pointwise
    {P : Type*} [AddCommGroup P] (F : TensorProduct S M N →+ P)
    (g : P →+ TensorProduct S M N)
    (h : ∀ x : M, ∀ y : N,
      g (F (x ⊗ₜ[S] y)) = x ⊗ₜ[S] y)
    (x : TensorProduct S M N) : g (F x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [F.map_zero, g.map_zero]
  | @tmul x y => exact h x y
  | @add x y hx hy =>
      rw [F.map_add, g.map_add]
      exact congrArg₂ (· + ·) hx hy

private lemma directSum_span_right_inverse
    {A M I : Type*} [CommRing A] [AddCommGroup M] [Module A M] [DecidableEq I]
    (CT : I → Submodule A M) (Gen : I → Set M)
    (hCT : ∀ i, CT i = Submodule.span A (Gen i))
    (F : M →+ (⨁ i, CT i))
    (hgen : ∀ i z (hz : z ∈ Gen i),
      F z = DirectSum.of (fun i => CT i) i
        ⟨z, (hCT i).symm ▸ Submodule.subset_span hz⟩)
    (hsmul : ∀ (c : A) (z : M), F (c • z) = c • F z) :
    F.comp (DirectSum.coeAddMonoidHom CT) = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro v
  induction v using DirectSum.induction_on with
  | zero =>
      exact F.map_zero.trans ((AddMonoidHom.id _).map_zero).symm
  | @of i x =>
      rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
        DirectSum.coeAddMonoidHom_of]
      have hx : (x : M) ∈ Submodule.span A (Gen i) := by
        rw [← hCT i]
        exact x.property
      refine Submodule.span_induction (p := fun z hz =>
        F z = DirectSum.of (fun i => CT i) i
          ⟨z, (hCT i).symm ▸ hz⟩) ?_ ?_ ?_ ?_ hx
      · intro z hz
        simpa only using hgen i z hz
      · exact F.map_zero.trans ((DirectSum.of (fun i => CT i) i).map_zero).symm
      · intro z z' hz hz' hz₁ hz₂
        have hzCT : z ∈ CT i := (hCT i).symm ▸ hz
        have hz'CT : z' ∈ CT i := (hCT i).symm ▸ hz'
        have hzadd : z + z' ∈ CT i :=
          (hCT i).symm ▸ (Submodule.add_mem _ hz hz')
        rw [F.map_add]
        calc
          F z + F z' =
              DirectSum.of (fun i => CT i) i ⟨z, hzCT⟩ +
                DirectSum.of (fun i => CT i) i ⟨z', hz'CT⟩ :=
            congrArg₂ (· + ·) hz₁ hz₂
          _ = DirectSum.of (fun i => CT i) i
              (⟨z, hzCT⟩ + ⟨z', hz'CT⟩) :=
            ((DirectSum.of (fun i => CT i) i).map_add _ _).symm
          _ = DirectSum.of (fun i => CT i) i
              ⟨z + z', hzadd⟩ := by rfl
      · intro c z hz hz₁
        have hzCT : z ∈ CT i := (hCT i).symm ▸ hz
        have hzsmul : c • z ∈ CT i :=
          (hCT i).symm ▸ (Submodule.smul_mem _ c hz)
        rw [hsmul c z]
        calc
          c • F z = c • DirectSum.of (fun i => CT i) i ⟨z, hzCT⟩ :=
            congrArg (fun w => c • w) hz₁
          _ = DirectSum.of (fun i => CT i) i (c • ⟨z, hzCT⟩) :=
            (DirectSum.of_smul A (M := fun i => CT i) i c
              (⟨z, hzCT⟩ : CT i)).symm
          _ = DirectSum.of (fun i => CT i) i
              ⟨c • z, hzsmul⟩ := by rfl
  | add z z' hz hz' =>
      simpa only [map_add] using congrArg₂ (· + ·) hz hz'

private lemma tensorProduct_homogeneous_generator
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (CT : ℤ → Submodule (degreeZeroSubring G) (TensorProduct S M N))
    (hCT : ∀ d, CT d = Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 d))
    (F₀ : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G]
      (⨁ d, CT d))
    (F : TensorProduct S M N →+ (⨁ d, CT d))
    (hF₀ : ∀ (i j : ℤ) (m : 𝓜.component i) (n : 𝓝.component j),
      ∃ w : CT (i + j),
        (w : TensorProduct S M N) = (m : M) ⊗ₜ[S] (n : N) ∧
          F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N)) =
            DirectSum.of (fun d => CT d) (i + j) w)
    (hF : ∀ (x : M) (y : N),
      F (x ⊗ₜ[S] y) = F₀ (x ⊗ₜ[degreeZeroSubring G] y)) :
    ∀ d z (hz : z ∈ tensorProductHomogeneousTensors G 𝓜 𝓝 d),
      F z = DirectSum.of (fun d => CT d) d
        ⟨z, (hCT d).symm ▸ Submodule.subset_span hz⟩ := by
  intro d z hz
  change ∃ i j : ℤ, i + j = d ∧ ∃ m, m ∈ 𝓜.component i ∧
    ∃ n, n ∈ 𝓝.component j ∧ TensorProduct.tmul S m n = z at hz
  rcases hz with ⟨i, j, hij, m, hm, n, hn, hmn⟩
  subst z
  rcases hF₀ i j ⟨m, hm⟩ ⟨n, hn⟩ with ⟨w, hw, hFw⟩
  rw [hF, hFw]
  subst d
  congr 1
  exact Subtype.ext hw

private lemma tensorProduct_recompose
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (CM : ℤ → Submodule (degreeZeroSubring G) M)
    (CN : ℤ → Submodule (degreeZeroSubring G) N)
    (hCM : ∀ i (_x : 𝓜.component i), CM i)
    (hCN : ∀ i (_x : 𝓝.component i), CN i)
    (hCM_val : ∀ i (x : 𝓜.component i), ((hCM i x : CM i) : M) = x)
    (hCN_val : ∀ i (x : 𝓝.component i), ((hCN i x : CN i) : N) = x)
    (hdecM : DirectSum.Decomposition CM)
    (hdecN : DirectSum.Decomposition CN)
    (CT : ℤ → Submodule (degreeZeroSubring G) (TensorProduct S M N))
    (F₀ : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G]
      (⨁ d, CT d))
    (q : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G]
      TensorProduct S M N)
    (coe : (⨁ d, CT d) →+ TensorProduct S M N)
    (hcoe : ∀ i (w : CT i),
      coe (DirectSum.of (fun d => CT d) i w) = (w : TensorProduct S M N))
    (_hCT : ∀ d, CT d = Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 d))
    (hF₀ : ∀ (i j : ℤ) (m : CM i) (n : CN j),
      ∃ w : CT (i + j),
        (w : TensorProduct S M N) = (m : M) ⊗ₜ[S] (n : N) ∧
          F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N)) =
            DirectSum.of (fun d => CT d) (i + j) w)
    (hq : ∀ (i j : ℤ) (m : CM i) (n : CN j),
      q ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N)) =
        (m : M) ⊗ₜ[S] (n : N)) :
    ∀ (x : M) (z : N),
      coe (F₀ (x ⊗ₜ[degreeZeroSubring G] z)) = q (x ⊗ₜ[degreeZeroSubring G] z) := by
  let _ : DirectSum.Decomposition CM := hdecM
  let _ : DirectSum.Decomposition CN := hdecN
  intro x z
  induction x using DirectSum.Decomposition.inductionOn
      (ℳ := 𝓜.component) with
  | zero => simp
  | add x y hx hy =>
      simpa only [TensorProduct.add_tmul, map_add] using congrArg₂ (· + ·) hx hy
  | @homogeneous i x =>
      induction z using DirectSum.Decomposition.inductionOn
          (ℳ := 𝓝.component) with
      | zero => simp
      | add z z' hz hz' =>
          simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hz'
      | @homogeneous j z =>
          rw [← hCM_val i x, ← hCN_val j z]
          rcases hF₀ i j (hCM i x) (hCN j z) with ⟨w, hw, hFw⟩
          rw [hFw, hcoe]
          exact hw.trans (hq i j (hCM i x) (hCN j z)).symm

private lemma tensorProduct_component_decomposition
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (CT : ℤ → Submodule (degreeZeroSubring G) (TensorProduct S M N))
    (hCT : ∀ d, CT d = Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 d))
    (F : TensorProduct S M N →+ (⨁ d, CT d))
    (hleft : (DirectSum.coeAddMonoidHom CT).comp F = AddMonoidHom.id _)
    (hright : F.comp (DirectSum.coeAddMonoidHom CT) = AddMonoidHom.id _) :
    Nonempty (DirectSum.Decomposition (tensorProductComponent G 𝓜 𝓝)) := by
  let emb : ∀ d, CT d →+ tensorProductComponent G 𝓜 𝓝 d := fun d =>
    { toFun := fun x => ⟨x, by
        change (x : TensorProduct S M N) ∈
          Submodule.span (degreeZeroSubring G)
            (tensorProductHomogeneousTensors G 𝓜 𝓝 d)
        rw [← hCT d]
        exact x.property⟩
      map_zero' := by rfl
      map_add' := by intro x y; rfl }
  let decomp : TensorProduct S M N →+
      (⨁ d, tensorProductComponent G 𝓜 𝓝 d) :=
    (DirectSum.map emb).comp F
  have hcoe :
      (DirectSum.coeAddMonoidHom (fun d => tensorProductComponent G 𝓜 𝓝 d)).comp
          (DirectSum.map emb) = DirectSum.coeAddMonoidHom CT := by
    apply AddMonoidHom.ext
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp
    | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw
    | @of d x => rfl
  refine ⟨DirectSum.Decomposition.ofAddHom
      (fun d => tensorProductComponent G 𝓜 𝓝 d) decomp ?_ ?_⟩
  · apply AddMonoidHom.ext
    intro x
    change ((DirectSum.coeAddMonoidHom
      (fun d => tensorProductComponent G 𝓜 𝓝 d)).comp
        (DirectSum.map emb)) (F x) = x
    rw [hcoe]
    exact DFunLike.congr_fun hleft x
  · apply AddMonoidHom.ext
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp [decomp]
    | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw
    | @of d x =>
        have hx : (x : TensorProduct S M N) ∈ CT d := by
          rw [hCT d]
          exact x.property
        let y : CT d := ⟨x, hx⟩
        have hy : DirectSum.coeAddMonoidHom CT
              (DirectSum.of (fun d => CT d) d y) = (x : TensorProduct S M N) := by
          rw [DirectSum.coeAddMonoidHom_of]
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
          DirectSum.coeAddMonoidHom_of, decomp]
        rw [← hy]
        have hF : F (DirectSum.coeAddMonoidHom CT
              (DirectSum.of (fun d => CT d) d y)) =
            DirectSum.of (fun d => CT d) d y :=
          DFunLike.congr_fun hright _
        rw [hF]
        rw [DirectSum.map_of]
        apply congrArg (DirectSum.of
          (fun d => tensorProductComponent G 𝓜 𝓝 d) d)
        apply Subtype.ext
        rfl

theorem tensorProduct_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Nonempty (DirectSum.Decomposition (tensorProductComponent G 𝓜 𝓝)) := by
  classical
  let : Module (degreeZeroSubring G) M :=
    Module.compHom M (SubringClass.subtype (degreeZeroSubring G))
  let : Module (degreeZeroSubring G) N :=
    Module.compHom N (SubringClass.subtype (degreeZeroSubring G))
  let : SMulCommClass S (degreeZeroSubring G) M := ⟨by
    intro s a x
    change (s : S) • ((a : S) • x) = (a : S) • (s • x)
    calc
      (s : S) • ((a : S) • x) = (s * (a : S)) • x :=
        (smul_assoc s (a : S) x).symm
      _ = ((a : S) * s) • x := by rw [mul_comm]
      _ = (a : S) • (s • x) := smul_assoc (a : S) s x⟩
  let : SMulCommClass S (degreeZeroSubring G) N := ⟨by
    intro s a x
    change (s : S) • ((a : S) • x) = (a : S) • (s • x)
    calc
      (s : S) • ((a : S) • x) = (s * (a : S)) • x :=
        (smul_assoc s (a : S) x).symm
      _ = ((a : S) * s) • x := by rw [mul_comm]
      _ = (a : S) • (s • x) := smul_assoc (a : S) s x⟩
  let : SMulCommClass (degreeZeroSubring G) S M :=
    SMulCommClass.symm S (degreeZeroSubring G) M
  let : SMulCommClass (degreeZeroSubring G) S N :=
    SMulCommClass.symm S (degreeZeroSubring G) N
  let : TensorProduct.CompatibleSMul S (degreeZeroSubring G) M N :=
    { smul_tmul := by
        intro a m n
        change ((a : S) • m) ⊗ₜ[S] n = m ⊗ₜ[S] ((a : S) • n)
        exact TensorProduct.smul_tmul (R := S) (R' := S) (a : S) m n }
  let CM : ℤ → Submodule (degreeZeroSubring G) M := fun i =>
    { carrier := 𝓜.component i
      zero_mem' := (𝓜.component i).zero_mem
      add_mem' := by
        intro x y hx hy
        exact (𝓜.component i).add_mem hx hy
      smul_mem' := by
        intro a x hx
        change (a : S) • x ∈ 𝓜.component i
        have h := 𝓜.gradedSMul.smul_mem a.property hx
        change (a : S) • x ∈ 𝓜.component ((0 : ℤ) + i) at h
        simpa using h }
  let CN : ℤ → Submodule (degreeZeroSubring G) N := fun i =>
    { carrier := 𝓝.component i
      zero_mem' := (𝓝.component i).zero_mem
      add_mem' := by
        intro x y hx hy
        exact (𝓝.component i).add_mem hx hy
      smul_mem' := by
        intro a x hx
        change (a : S) • x ∈ 𝓝.component i
        have h := 𝓝.gradedSMul.smul_mem a.property hx
        change (a : S) • x ∈ 𝓝.component ((0 : ℤ) + i) at h
        simpa using h }
  let embM : ∀ i, 𝓜.component i →+ CM i := fun i =>
    { toFun := fun x => ⟨x, by simp [CM]⟩
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl }
  let embN : ∀ i, 𝓝.component i →+ CN i := fun i =>
    { toFun := fun x => ⟨x, by simp [CN]⟩
      map_zero' := by ext; rfl
      map_add' := by intro x y; ext; rfl }
  let decompM : M →+ (⨁ i, CM i) :=
    (DirectSum.map embM).comp (DirectSum.decomposeAddEquiv 𝓜.component).toAddMonoidHom
  let decompN : N →+ (⨁ i, CN i) :=
    (DirectSum.map embN).comp (DirectSum.decomposeAddEquiv 𝓝.component).toAddMonoidHom
  have hleftM :
      (DirectSum.coeAddMonoidHom CM).comp decompM = AddMonoidHom.id M := by
    ext x
    induction x using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp [decompM]
    | homogeneous x => simp [decompM, embM]
    | add x y hx hy =>
        calc
          (DirectSum.coeAddMonoidHom CM) (decompM (x + y)) =
              (DirectSum.coeAddMonoidHom CM) (decompM x) +
                (DirectSum.coeAddMonoidHom CM) (decompM y) :=
            by
              rw [map_add decompM]
              exact (DirectSum.coeAddMonoidHom CM).map_add _ _
          _ = x + y := by
            change ((DirectSum.coeAddMonoidHom CM).comp decompM) x +
              ((DirectSum.coeAddMonoidHom CM).comp decompM) y = _
            simpa only [AddMonoidHom.id_apply] using congrArg₂ (· + ·) hx hy
  have hrightM :
      decompM.comp (DirectSum.coeAddMonoidHom CM) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      DirectSum.coeAddMonoidHom_of]
    simp [decompM, embM]
  have hleftN :
      (DirectSum.coeAddMonoidHom CN).comp decompN = AddMonoidHom.id N := by
    ext x
    induction x using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓝.component) with
    | zero => simp [decompN]
    | homogeneous x => simp [decompN, embN]
    | add x y hx hy =>
        calc
          (DirectSum.coeAddMonoidHom CN) (decompN (x + y)) =
              (DirectSum.coeAddMonoidHom CN) (decompN x) +
                (DirectSum.coeAddMonoidHom CN) (decompN y) :=
            by
              rw [map_add decompN]
              exact (DirectSum.coeAddMonoidHom CN).map_add _ _
          _ = x + y := by
            change ((DirectSum.coeAddMonoidHom CN).comp decompN) x +
              ((DirectSum.coeAddMonoidHom CN).comp decompN) y = _
            simpa only [AddMonoidHom.id_apply] using congrArg₂ (· + ·) hx hy
  have hrightN :
      decompN.comp (DirectSum.coeAddMonoidHom CN) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply,
      DirectSum.coeAddMonoidHom_of]
    simp [decompN, embN]
  let hdecM : DirectSum.Decomposition CM :=
    DirectSum.Decomposition.ofAddHom CM decompM hleftM hrightM
  let _ : DirectSum.Decomposition CM := hdecM
  let hdecN : DirectSum.Decomposition CN :=
    DirectSum.Decomposition.ofAddHom CN decompN hleftN hrightN
  let _ : DirectSum.Decomposition CN := hdecN
  let CT : ℤ → Submodule (degreeZeroSubring G) (TensorProduct S M N) :=
    fun d => Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 d)
  let q : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G]
      TensorProduct S M N :=
    TensorProduct.mapOfCompatibleSMul S (degreeZeroSubring G) (degreeZeroSubring G) M N
  let pairMap : ∀ (i j : ℤ),
      (TensorProduct (degreeZeroSubring G) (CM i) (CN j)) →ₗ[degreeZeroSubring G]
      TensorProduct S M N := fun i j =>
    q.comp (TensorProduct.map (CM i).subtype (CN j).subtype)
  let pairMapCT : ∀ (i j : ℤ),
      (TensorProduct (degreeZeroSubring G) (CM i) (CN j)) →ₗ[degreeZeroSubring G] CT (i + j) :=
    fun i j => LinearMap.codRestrict (CT (i + j)) (pairMap i j) (by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => exact (CT (i + j)).zero_mem
      | add x y hx hy =>
          simpa only [map_add] using (CT (i + j)).add_mem hx hy
      | tmul x y =>
          refine Submodule.subset_span ?_
          exact ⟨i, j, rfl, x, x.property, y, y.property, by
            simp [pairMap, q]⟩)
  let directSumEquiv :
      (TensorProduct (degreeZeroSubring G) (⨁ i, CM i) (⨁ j, CN j)) ≃ₗ[degreeZeroSubring G]
        (⨁ p : ℤ × ℤ,
          TensorProduct (degreeZeroSubring G) (CM p.1) (CN p.2)) :=
    TensorProduct.directSum (R := degreeZeroSubring G) (S := degreeZeroSubring G)
      (ι₁ := ℤ) (ι₂ := ℤ) (M₁ := fun i => CM i) (M₂ := fun j => CN j)
  let sourceEquiv :
      TensorProduct (degreeZeroSubring G) M N ≃ₗ[degreeZeroSubring G]
        (⨁ p : ℤ × ℤ,
          TensorProduct (degreeZeroSubring G) (CM p.1) (CN p.2)) :=
    (TensorProduct.congr (DirectSum.decomposeLinearEquiv CM)
      (DirectSum.decomposeLinearEquiv CN)).trans
      directSumEquiv
  let g : (⨁ p : ℤ × ℤ,
      TensorProduct (degreeZeroSubring G) (CM p.1) (CN p.2)) →ₗ[degreeZeroSubring G]
        (⨁ d, CT d) :=
    DirectSum.toModule (degreeZeroSubring G) _ _ fun p =>
      (DirectSum.lof (degreeZeroSubring G) ℤ (fun d => CT d) (p.1 + p.2)).comp
        (pairMapCT p.1 p.2)
  let F₀ : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G]
      (⨁ d, CT d) :=
    g.comp sourceEquiv.toLinearMap
  have hF₀_hom (i j : ℤ) (m : CM i) (n : CN j) :
      F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N)) =
        DirectSum.of (fun d => CT d) (i + j)
          ⟨(m : M) ⊗ₜ[S] (n : N), Submodule.subset_span
            ⟨i, j, rfl, m, m.property, n, n.property, rfl⟩⟩ := by
    simp [F₀, sourceEquiv, directSumEquiv, g, pairMapCT, pairMap, q,
      TensorProduct.directSum_lof_tmul_lof, LinearMap.codRestrict]
    rw [DirectSum.lof_eq_of]
  let f : M →+ N →+ (⨁ d, CT d) :=
    { toFun := fun m =>
        { toFun := fun n => F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N))
          map_zero' := by simp
          map_add' := by
            intro x y
            change F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (x + y)) = _
            simpa only [TensorProduct.tmul_add] using
              F₀.map_add ((m : M) ⊗ₜ[degreeZeroSubring G] x)
                ((m : M) ⊗ₜ[degreeZeroSubring G] y) }
      map_zero' := by ext; simp
      map_add' := by
        intro x y
        apply AddMonoidHom.ext
        intro n
        change F₀ (((x : M) + y) ⊗ₜ[degreeZeroSubring G] n) =
          F₀ ((x : M) ⊗ₜ[degreeZeroSubring G] n) +
            F₀ ((y : M) ⊗ₜ[degreeZeroSubring G] n)
        simpa only [TensorProduct.add_tmul] using
          F₀.map_add ((x : M) ⊗ₜ[degreeZeroSubring G] n)
            ((y : M) ⊗ₜ[degreeZeroSubring G] n) }
  let : DirectSum.Decomposition (ringModuleComponent G) :=
    Classical.choice (ringModule_decomposition_exists G)
  have hbal : ∀ (s : S) (m : M) (n : N), f (s • m) n = f m (s • n) := by
    intro s m n
    induction s using DirectSum.Decomposition.inductionOn
        (ℳ := ringModuleComponent G) with
    | zero => simp [f]
    | add s t hs ht =>
        simpa [f, add_smul, TensorProduct.add_tmul, TensorProduct.tmul_add] using
          congrArg₂ (· + ·) hs ht
    | @homogeneous k s =>
        induction m using DirectSum.Decomposition.inductionOn
            (ℳ := 𝓜.component) with
        | zero => simp [f]
        | add m m' hm hm' =>
            simpa [f, smul_add, TensorProduct.add_tmul, TensorProduct.tmul_add] using
              congrArg₂ (· + ·) hm hm'
        | @homogeneous i m =>
            induction n using DirectSum.Decomposition.inductionOn
                (ℳ := 𝓝.component) with
            | zero => simp [f]
            | add n n' hn hn' =>
                simpa [f, smul_add, TensorProduct.tmul_add, TensorProduct.add_tmul] using
                  congrArg₂ (· + ·) hn hn'
            | @homogeneous j n =>
                by_cases hk : 0 ≤ k
                · have hs : (s : S) ∈ G.component k.toNat := by
                    simpa [ringModuleComponent, hk] using s.property
                  have hsm : (s : S) • (m : M) ∈ 𝓜.component (k + i) := by
                    have h := 𝓜.gradedSMul.smul_mem hs m.property
                    change (s : S) • (m : M) ∈
                      𝓜.component ((k.toNat : ℤ) + i) at h
                    simpa [Int.toNat_of_nonneg hk] using h
                  have hsn : (s : S) • (n : N) ∈ 𝓝.component (k + j) := by
                    have h := 𝓝.gradedSMul.smul_mem hs n.property
                    change (s : S) • (n : N) ∈
                      𝓝.component ((k.toNat : ℤ) + j) at h
                    simpa [Int.toNat_of_nonneg hk] using h
                  change F₀ (((s : S) • (m : M)) ⊗ₜ[degreeZeroSubring G] (n : N)) =
                    F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] ((s : S) • (n : N)))
                  rw [hF₀_hom (k + i) j ⟨(s : S) • (m : M), hsm⟩ n,
                    hF₀_hom i (k + j) m ⟨(s : S) • (n : N), hsn⟩]
                  /- Prior attempt: the dependent `DirectSum.of` terms require
                     transporting both the degree and its membership proof. -/
                  change DFinsupp.single (k + i + j) _ =
                    DFinsupp.single (i + (k + j)) _
                  rw [DFinsupp.single_eq_single_iff]
                  left
                  have hdeg : k + i + j = i + (k + j) := by omega
                  constructor
                  · exact hdeg
                  · apply (Subtype.heq_iff_coe_eq (fun x => by
                      simp [CT, hdeg])).2
                    simp [TensorProduct.smul_tmul]
                · have hs0 : (s : S) = 0 := by
                    simpa [ringModuleComponent, hk] using s.property
                  simp [hs0]
  let F : TensorProduct S M N →+ (⨁ d, CT d) := TensorProduct.liftAddHom f hbal
  let coe : (⨁ d, CT d) →+ TensorProduct S M N := DirectSum.coeAddMonoidHom CT
  have hf (x : M) (y : N) :
      f x y = F₀ (x ⊗ₜ[degreeZeroSubring G] y) := rfl
  have hF_tmul (x : M) (y : N) : F (x ⊗ₜ[S] y) = f x y :=
    TensorProduct.liftAddHom_tmul f hbal x y
  have hF₀_hom_recompose (x : M) (z : N) :
      coe (F₀ (x ⊗ₜ[degreeZeroSubring G] z)) = q (x ⊗ₜ[degreeZeroSubring G] z) :=
    tensorProduct_recompose G 𝓜 𝓝 CM CN
      (fun i x => (⟨x, by
        change (x : M) ∈ 𝓜.component i
        exact x.property⟩ : CM i))
      (fun i z => (⟨z, by
        change (z : N) ∈ 𝓝.component i
        exact z.property⟩ : CN i))
      (fun i x => rfl) (fun i z => rfl) hdecM hdecN CT F₀ q coe
      (fun i w => DirectSum.coeAddMonoidHom_of CT i w)
      (fun d => by rfl)
      (fun i j m n => by
        refine ⟨_, ?_, hF₀_hom i j m n⟩
        rfl)
      (fun i j m n => by
        rfl) x z
  have hleft : coe.comp F = AddMonoidHom.id _ := by
    /- Prior attempt: the tensor-product induction depended on the
       recomposition equality above. -/
    have hpoint : ∀ x : TensorProduct S M N, coe (F x) = x := by
      intro x
      apply tensorProduct_addHom_pointwise F coe
      intro x y
      rw [hF_tmul x y, hf]
      simpa only [q, TensorProduct.mapOfCompatibleSMul_tmul] using
        hF₀_hom_recompose x y
    apply AddMonoidHom.ext
    intro x
    have hcomp : (coe.comp F) x = coe (F x) := rfl
    have hid : (AddMonoidHom.id _) x = x := rfl
    exact hcomp.trans ((hpoint x).trans hid.symm)
  have hF' (x : M) (y : N) :
      F (x ⊗ₜ[S] y) = F₀ (x ⊗ₜ[degreeZeroSubring G] y) :=
    (hF_tmul x y).trans (hf x y)
  have hgen := tensorProduct_homogeneous_generator G 𝓜 𝓝 CT
      (fun d => by rfl) F₀ F
      (fun i j m n => by
        have hm' : (m : M) ∈ CM i := by
          change (m : M) ∈ 𝓜.component i
          exact m.property
        have hn' : (n : N) ∈ CN j := by
          change (n : N) ∈ 𝓝.component j
          exact n.property
        refine ⟨_, ?_, hF₀_hom i j ⟨m, hm'⟩ ⟨n, hn'⟩⟩
        rfl)
      hF'
  have hF_smul (c : degreeZeroSubring G) (x : TensorProduct S M N) :
      F ((c : S) • x) = c • F x := by
    apply tensorProduct_smul_of_tmul G F c
    intro m n
    rw [TensorProduct.smul_tmul', hF_tmul, hF_tmul, hbal, hf, hf]
    calc
      F₀ (m ⊗ₜ[degreeZeroSubring G] ((c : S) • n)) =
          F₀ ((c : degreeZeroSubring G) •
            (m ⊗ₜ[degreeZeroSubring G] n)) := by
        apply congrArg F₀
        calc
          m ⊗ₜ[degreeZeroSubring G] ((c : S) • n) =
              ((c : degreeZeroSubring G) • m) ⊗ₜ[degreeZeroSubring G] n := by
            change m ⊗ₜ[degreeZeroSubring G] (c • n) =
              ((c : degreeZeroSubring G) • m) ⊗ₜ[degreeZeroSubring G] n
            exact
              (TensorProduct.smul_tmul (R := degreeZeroSubring G)
                (R' := degreeZeroSubring G) c m n).symm
          _ = (c : degreeZeroSubring G) •
              (m ⊗ₜ[degreeZeroSubring G] n) := by
            rfl
      _ = c • F₀ (m ⊗ₜ[degreeZeroSubring G] n) :=
        by
          rw [map_smul]
  have hright : F.comp coe = AddMonoidHom.id _ := by
    /- Prior attempt: the span induction did not retain the component
       family through the dependent direct-sum coercion. -/
    refine directSum_span_right_inverse
      (A := degreeZeroSubring G) (M := TensorProduct S M N) (I := ℤ)
      CT (fun d => tensorProductHomogeneousTensors G 𝓜 𝓝 d)
      (fun d => by rfl) F hgen hF_smul
  /- Prior attempt: the constructed direct sum uses submodule subtypes,
     while the theorem's decomposition is indexed by add-subgroup subtypes. -/
  apply tensorProduct_component_decomposition G 𝓜 𝓝 CT
  · intro d
    rfl
  · exact hleft
  · exact hright

theorem tensorProduct_gradedSMul
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    SetLike.GradedSMul G.component (tensorProductComponent G 𝓜 𝓝) := by
  refine { smul_mem := ?_ }
  intro i j a b ha hb
  change (a : S) • b ∈
    Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j))
  change b ∈ Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 j) at hb
  refine Submodule.span_induction (p := fun x _ =>
      (a : S) • x ∈ Submodule.span (degreeZeroSubring G)
        (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j))) ?_ ?_ ?_ ?_ hb
  · intro z hz
    rcases hz with ⟨k, l, hkl, m, hm, n, hn, hmn⟩
    rw [← hmn, TensorProduct.smul_tmul']
    refine Submodule.subset_span ?_
    refine ⟨i +ᵥ k, l, ?_, (a : S) • m, 𝓜.gradedSMul.smul_mem ha hm, n, hn, rfl⟩
    change (i : ℤ) + k + l = (i : ℤ) + j
    rw [add_assoc, hkl]
  · simp
  · intro x y hx hy ihx ihy
    rw [smul_add]
    exact Submodule.add_mem
      (Submodule.span (degreeZeroSubring G)
        (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j))) ihx ihy
  · intro c x hx ih
    have h := Submodule.smul_mem
      (Submodule.span (degreeZeroSubring G)
        (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j))) c ih
    change (c : S) • ((a : S) • x) ∈
      Submodule.span (degreeZeroSubring G)
        (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j)) at h
    change (a : S) • ((c : S) • x) ∈
      Submodule.span (degreeZeroSubring G)
        (tensorProductHomogeneousTensors G 𝓜 𝓝 (i +ᵥ j))
    have heq : (a : S) • ((c : S) • x) = (c : S) • ((a : S) • x) := by
      rw [← smul_assoc, ← smul_assoc, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [heq]
    exact h

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
  have hcomp : ∀ d : ℤ,
      tensorProductComponent G 𝓜 𝓝 (n + d) =
        tensorProductComponent G 𝓜 (twist G 𝓝 n) d := by
    intro d
    have hset :
        tensorProductHomogeneousTensors G 𝓜 𝓝 (n + d) =
          tensorProductHomogeneousTensors G 𝓜 (twist G 𝓝 n) d := by
      ext z
      constructor
      · rintro ⟨i, j, hij, m, hm, k, hk, hmk⟩
        refine ⟨i, j - n, ?_, m, hm, k, ?_, hmk⟩
        · have h := congrArg (fun x : ℤ => x - n) hij
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
        · simpa [twist] using hk
      · rintro ⟨i, j, hij, m, hm, k, hk, hmk⟩
        refine ⟨i, n + j, ?_, m, hm, k, ?_, hmk⟩
        · have h := congrArg (fun x : ℤ => n + x) hij
          simpa [add_assoc, add_comm, add_left_comm] using h
        · simpa [twist] using hk
    unfold tensorProductComponent
    rw [hset]
  let e : GradedLinearEquiv G
      (twist G (tensorProductGradedModule G 𝓜 𝓝) n)
      (tensorProductGradedModule G 𝓜 (twist G 𝓝 n)) :=
    { toLinearEquiv := LinearEquiv.refl S (TensorProduct S M N)
      map_component' := by
        intro d x hx
        change x ∈ tensorProductComponent G 𝓜 𝓝 (n + d) at hx
        change x ∈ tensorProductComponent G 𝓜 (twist G 𝓝 n) d
        exact hcomp d ▸ hx
      inv_component' := by
        intro d x hx
        change x ∈ tensorProductComponent G 𝓜 (twist G 𝓝 n) d at hx
        change x ∈ tensorProductComponent G 𝓜 𝓝 (n + d)
        exact (hcomp d).symm ▸ hx }
  exact ⟨e⟩

theorem twist_tensorProduct_left_isomorphism
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N)
    (n : ℤ) :
    Nonempty (GradedLinearEquiv G
      (twist G (tensorProductGradedModule G 𝓜 𝓝) n)
      (tensorProductGradedModule G (twist G 𝓜 n) 𝓝)) := by
  have hcomp : ∀ d : ℤ,
      tensorProductComponent G 𝓜 𝓝 (n + d) =
        tensorProductComponent G (twist G 𝓜 n) 𝓝 d := by
    intro d
    have hset :
        tensorProductHomogeneousTensors G 𝓜 𝓝 (n + d) =
          tensorProductHomogeneousTensors G (twist G 𝓜 n) 𝓝 d := by
      ext z
      constructor
      · rintro ⟨i, j, hij, m, hm, k, hk, hmk⟩
        refine ⟨i - n, j, ?_, m, ?_, k, hk, hmk⟩
        · have h := congrArg (fun x : ℤ => x - n) hij
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
        · simpa [twist] using hm
      · rintro ⟨i, j, hij, m, hm, k, hk, hmk⟩
        refine ⟨n + i, j, ?_, m, ?_, k, hk, hmk⟩
        · have h := congrArg (fun x : ℤ => n + x) hij
          simpa [add_assoc, add_comm, add_left_comm] using h
        · simpa [twist] using hm
    unfold tensorProductComponent
    rw [hset]
  let e : GradedLinearEquiv G
      (twist G (tensorProductGradedModule G 𝓜 𝓝) n)
      (tensorProductGradedModule G (twist G 𝓜 n) 𝓝) :=
    { toLinearEquiv := LinearEquiv.refl S (TensorProduct S M N)
      map_component' := by
        intro d x hx
        change x ∈ tensorProductComponent G 𝓜 𝓝 (n + d) at hx
        change x ∈ tensorProductComponent G (twist G 𝓜 n) 𝓝 d
        exact hcomp d ▸ hx
      inv_component' := by
        intro d x hx
        change x ∈ tensorProductComponent G (twist G 𝓜 n) 𝓝 d at hx
        change x ∈ tensorProductComponent G 𝓜 𝓝 (n + d)
        exact (hcomp d).symm ▸ hx }
  exact ⟨e⟩

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
  let H : ℤ → Submodule (degreeZeroSubring G) (M →ₗ[S] N) :=
    fun n => gradedHomZero G 𝓜 (twist G 𝓝 n)
  let _ : AddAction ℕ ℤ :=
    { vadd := fun n m => (n : ℤ) + m
      add_vadd := by
        intro n m z
        change ((n + m : ℕ) : ℤ) + z = (n : ℤ) + ((m : ℤ) + z)
        simp only [Int.natCast_add, add_assoc]
      zero_vadd := by
        intro z
        change (0 : ℤ) + z = z
        exact zero_add z }
  let _ : SetLike.GradedSMul (fun n : ℕ => G.component n) H :=
    { smul_mem := by
        intro i j a f ha hf d x hx
        have hfd := hf d x hx
        change (a : S) • (f : M →ₗ[S] N) x ∈
          (twist G 𝓝 (i +ᵥ j)).component d
        change (a : S) • (f : M →ₗ[S] N) x ∈
          𝓝.component ((i : ℤ) + j + d)
        have h := 𝓝.gradedSMul.smul_mem ha hfd
        change (a : S) • (f : M →ₗ[S] N) x ∈
          𝓝.component ((i : ℤ) + ((j : ℤ) + d)) at h
        simpa only [add_assoc] using h }
  exact ⟨SetLike.gmodule (fun n : ℕ => G.component n) (fun n : ℤ => H n)⟩

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

private lemma graded_finite_homogeneous_generators
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Module.Finite S M] :
    ∃ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M),
      (∀ i, x i ∈ 𝓜.component (d i)) ∧
        Submodule.span S (Set.range x) = ⊤ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := M)
  let ι := Σ i : Fin n, (DirectSum.decompose 𝓜.component (s i)).support
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let d : Fin (Fintype.card ι) → ℤ := fun k => (e.symm k).2
  let x : Fin (Fintype.card ι) → M := fun k =>
    (DirectSum.decompose 𝓜.component (s (e.symm k).1) (e.symm k).2 : M)
  refine ⟨Fintype.card ι, d, x, ?_, ?_⟩
  · intro k
    exact (DirectSum.decompose 𝓜.component (s (e.symm k).1) (e.symm k).2).property
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.2
    rintro y ⟨i, rfl⟩
    rw [← DirectSum.sum_support_decompose 𝓜.component (s i)]
    apply (Submodule.span S (Set.range x)).sum_mem
    intro j hj
    apply Submodule.subset_span
    refine ⟨e ⟨i, ⟨j, hj⟩⟩, ?_⟩
    dsimp [x]
    rw [e.symm_apply_apply]

private lemma graded_lower_components_zero
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (k : ℤ)
    (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M)
    (hx : ∀ i, x i ∈ 𝓜.component (d i))
    (hk : ∀ i, x i ≠ 0 → k ≤ d i)
    (hspan : Submodule.span S (Set.range x) = ⊤) :
    ∀ (y : M) (e : ℤ), e < k →
      (DirectSum.decompose 𝓜.component y e : M) = 0 := by
  let 𝓡 := ringAsGradedModule G
  let _ : DirectSum.Decomposition (ringModuleComponent G) := 𝓡.decomposition
  have hproperty : ∀ y : M, ∀ e : ℤ, e < k →
      (DirectSum.decompose 𝓜.component y e : M) = 0 := by
    intro y
    have hy : y ∈ Submodule.span S (Set.range x) := by
      rw [hspan]
      trivial
    have hdecomp_add (u v : M) :
        DirectSum.decompose 𝓜.component (u + v) =
          DirectSum.decompose 𝓜.component u + DirectSum.decompose 𝓜.component v :=
      (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
    refine Submodule.span_induction (p := fun y _ => ∀ e : ℤ, e < k →
        (DirectSum.decompose 𝓜.component y e : M) = 0) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩ e he
      by_cases hxi : x i = 0
      · simp [hxi]
      · exact DirectSum.decompose_of_mem_ne 𝓜.component (hx i)
          (ne_of_gt (lt_of_lt_of_le he (hk i hxi)))
    · intro e he
      simp
    · intro y z _ _ hy hz e he
      rw [hdecomp_add]
      change (DirectSum.decompose 𝓜.component y e : M) +
        (DirectSum.decompose 𝓜.component z e : M) = 0
      rw [hy e he, hz e he]
      simp
    · intro a y _ hy e he
      induction a using DirectSum.Decomposition.inductionOn
          (ℳ := ringModuleComponent G) with
      | zero => simp
      | add a b ha hb =>
          rw [add_smul, hdecomp_add]
          change (DirectSum.decompose 𝓜.component (a • y) e : M) +
            (DirectSum.decompose 𝓜.component (b • y) e : M) = 0
          rw [ha, hb, add_zero]
      | @homogeneous i a =>
          by_cases hi : i < 0
          · have ha0 : (a : S) = 0 := by
              have ha' : (a : S) ∈ (⊥ : AddSubgroup S) := by
                rw [← ringModuleComponent_of_negative G hi]
                exact a.property
              simpa using ha'
            simp [ha0]
          · have hi' : 0 ≤ i := le_of_not_gt hi
            have ha' : (a : S) ∈ G.component i.toNat := by
              rw [← ringModuleComponent_of_nonnegative G hi']
              exact a.property
            have hproj : ∀ e : ℤ, ∀ z : M,
                (DirectSum.decompose 𝓜.component ((a : S) • z) e : M) =
                  (a : S) •
                    (DirectSum.decompose 𝓜.component z (e - (i.toNat : ℤ)) : M) := by
              intro e z
              induction z using DirectSum.Decomposition.inductionOn
                  (ℳ := 𝓜.component) with
              | zero => simp
              | add z w hz hw =>
                  rw [smul_add, hdecomp_add ((a : S) • z) ((a : S) • w),
                    hdecomp_add z w]
                  change (DirectSum.decompose 𝓜.component ((a : S) • z) e : M) +
                      (DirectSum.decompose 𝓜.component ((a : S) • w) e : M) =
                    (a : S) •
                      ((DirectSum.decompose 𝓜.component z (e - (i.toNat : ℤ)) : M) +
                        (DirectSum.decompose 𝓜.component w (e - (i.toNat : ℤ)) : M))
                  rw [hz, hw, smul_add]
              | @homogeneous j z =>
                  have hmul := 𝓜.gradedSMul.smul_mem ha' z.property
                  have hmul' : (a : S) • (z : M) ∈
                      𝓜.component ((i.toNat : ℤ) + j) := by
                    change (a : S) • (z : M) ∈
                      𝓜.component ((i.toNat : ℤ) + j) at hmul
                    exact hmul
                  by_cases hdeg : (i.toNat : ℤ) + j = e
                  · have hjeq : e - (i.toNat : ℤ) = j := by omega
                    have hjeq' : (i.toNat : ℤ) + j - (i.toNat : ℤ) = j := by omega
                    rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component hmul', hjeq',
                      DirectSum.decompose_of_mem_same 𝓜.component z.property]
                  · have hjeq : j ≠ e - (i.toNat : ℤ) := by omega
                    rw [DirectSum.decompose_of_mem_ne 𝓜.component hmul' hdeg,
                      DirectSum.decompose_of_mem_ne 𝓜.component z.property hjeq]
                    simp
            rw [hproj e y]
            have hlow : e - (i.toNat : ℤ) < k := by
              have hnonneg : 0 ≤ (i.toNat : ℤ) := Int.natCast_nonneg _
              omega
            rw [hy (e - (i.toNat : ℤ)) hlow, smul_zero]
  exact hproperty

private lemma ringModule_zero_component_eq
    (G : GradedRingData S)
    (hdec : DirectSum.Decomposition (ringModuleComponent G)) (r : S) :
    (hdec.decompose' r 0 : S) =
      (DirectSum.decompose G.component r 0 : S) := by
  let f : (⨁ d : ℤ, ringModuleComponent G d) →+ S :=
    { toFun := fun z =>
        (DirectSum.decompose G.component
          (DirectSum.coeAddMonoidHom (ringModuleComponent G) z) 0 : S)
      map_zero' := by simp
      map_add' := by
        intro z w
        simp [DirectSum.decompose_add] }
  let g : (⨁ d : ℤ, ringModuleComponent G d) →+ S :=
    { toFun := fun z => (z 0 : S)
      map_zero' := by simp
      map_add' := by
        intro z w
        rfl }
  have hfg : f = g := by
    apply DirectSum.addHom_ext
    intro i a
    by_cases hi : 0 ≤ i
    · have ha : (a : S) ∈ G.component i.toNat := by
        simpa [ringModuleComponent, hi] using a.property
      by_cases hi0 : i = 0
      · subst i
        have hg_of : g (DirectSum.of (fun d : ℤ => ringModuleComponent G d) 0 a) =
            (a : S) := by rfl
        rw [hg_of]
        simp [f, DirectSum.coeAddMonoidHom_of,
          DirectSum.decompose_of_mem _ ha]
      · have hnat : i.toNat ≠ 0 := by omega
        have hg_of : g (DirectSum.of (fun d : ℤ => ringModuleComponent G d) i a) =
            ((DirectSum.of (fun d : ℤ => ringModuleComponent G d) i a) 0 : S) := by
          rfl
        rw [hg_of]
        simp [f, DirectSum.coeAddMonoidHom_of,
          DirectSum.decompose_of_mem _ ha, DirectSum.of_apply, hnat, hi0]
    · have ha0 : (a : S) = 0 := by
        simpa [ringModuleComponent, hi] using a.property
      have hi0 : i ≠ 0 := by omega
      have hg_of : g (DirectSum.of (fun d : ℤ => ringModuleComponent G d) i a) =
          ((DirectSum.of (fun d : ℤ => ringModuleComponent G d) i a) 0 : S) := by
        rfl
      rw [hg_of]
      simp [f, DirectSum.coeAddMonoidHom_of, DirectSum.of_apply, ha0, hi0]
  have hleft := hdec.left_inv r
  have hproj := congrArg (fun z : S =>
    (DirectSum.decompose G.component z 0 : S)) hleft
  calc
    (hdec.decompose' r 0 : S) = g (hdec.decompose' r) := by rfl
    _ = f (hdec.decompose' r) := by rw [hfg]
    _ = (DirectSum.decompose G.component r 0 : S) := by
      change
        (DirectSum.decompose G.component
          (DirectSum.coeAddMonoidHom (ringModuleComponent G)
            (hdec.decompose' r)) 0 : S) =
          (DirectSum.decompose G.component r 0 : S)
      exact hproj

private lemma graded_smul_component_formula
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (k : ℤ)
    (hdec : DirectSum.Decomposition (ringModuleComponent G))
    (hlow : ∀ (y : M) (e : ℤ), e < k →
      (DirectSum.decompose 𝓜.component y e : M) = 0) :
    ∀ (r : S) (y : M),
      (DirectSum.decompose 𝓜.component (r • y) k : M) =
        (hdec.decompose' r 0 : S) •
          (DirectSum.decompose 𝓜.component y k : M) := by
  let _ : DirectSum.Decomposition (ringModuleComponent G) := hdec
  have hdecomp_add (u v : M) :
      DirectSum.decompose 𝓜.component (u + v) =
        DirectSum.decompose 𝓜.component u + DirectSum.decompose 𝓜.component v :=
    (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
  have hhom : ∀ (i : ℤ) (a : ringModuleComponent G i), 0 ≤ i → ∀ y : M,
      (DirectSum.decompose 𝓜.component ((a : S) • y) k : M) =
        (a : S) •
          (DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) := by
    intro i a hi y
    have ha : (a : S) ∈ G.component i.toNat := by
      rw [← ringModuleComponent_of_nonnegative G hi]
      exact a.property
    induction y using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp
    | add y z hy hz =>
        rw [smul_add, hdecomp_add ((a : S) • y) ((a : S) • z),
          hdecomp_add y z]
        change (DirectSum.decompose 𝓜.component ((a : S) • y) k : M) +
            (DirectSum.decompose 𝓜.component ((a : S) • z) k : M) =
          (a : S) •
            ((DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) +
              (DirectSum.decompose 𝓜.component z (k - (i.toNat : ℤ)) : M))
        rw [hy, hz, smul_add]
    | @homogeneous j y =>
        have hmul := 𝓜.gradedSMul.smul_mem ha y.property
        have hmul' : (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) := by
          change (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) at hmul
          exact hmul
        by_cases hdeg : (i.toNat : ℤ) + j = k
        · have hjeq : (i.toNat : ℤ) + j - (i.toNat : ℤ) = j := by omega
          rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component hmul',
            hjeq, DirectSum.decompose_of_mem_same 𝓜.component y.property]
        · have hjeq : j ≠ k - (i.toNat : ℤ) := by omega
          rw [DirectSum.decompose_of_mem_ne 𝓜.component hmul' hdeg,
            DirectSum.decompose_of_mem_ne 𝓜.component y.property hjeq]
          simp
  have hrdecomp_add (r s : S) :
      hdec.decompose' (r + s) = hdec.decompose' r + hdec.decompose' s :=
    (DirectSum.decomposeAddEquiv (ringModuleComponent G)).map_add r s
  intro r y
  induction r using DirectSum.Decomposition.inductionOn
      (ℳ := ringModuleComponent G) with
  | zero => simp
  | add r s hr hs =>
      rw [add_smul, hdecomp_add ((r : S) • y) ((s : S) • y), hrdecomp_add]
      change (DirectSum.decompose 𝓜.component (r • y) k : M) +
          (DirectSum.decompose 𝓜.component (s • y) k : M) =
        ((hdec.decompose' r 0 : S) + (hdec.decompose' s 0 : S)) •
            (DirectSum.decompose 𝓜.component y k : M)
      rw [hr, hs, add_smul]
  | @homogeneous i r =>
      by_cases hi : i < 0
      · have hr0 : (r : S) = 0 := by
          have hr' : (r : S) ∈ (⊥ : AddSubgroup S) := by
            rw [← ringModuleComponent_of_negative G hi]
            exact r.property
          simpa using hr'
        simp [hr0]
      · by_cases hi0 : i = 0
        · subst i
          have hr0 : (hdec.decompose' (r : S) 0 : S) = (r : S) := by
            have h := DirectSum.decompose_of_mem_same
              (ringModuleComponent G) r.property
            change (hdec.decompose' (r : S) 0 : S) = (r : S) at h
            exact h
          have hm := hhom 0 r (by rfl) y
          rw [hr0]
          have hzero : k - (Int.toNat (0 : ℤ) : ℤ) = k := by omega
          rw [hzero] at hm
          exact hm
        · have hi' : 0 < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hi0)
          have hm := hhom i r (le_of_lt hi') y
          rw [hm]
          have hlow' : k - (i.toNat : ℤ) < k := by
            have hcast : (i.toNat : ℤ) = i := Int.toNat_of_nonneg (le_of_lt hi')
            have hpos : 0 < i.toNat := by omega
            omega
          rw [hlow y (k - (i.toNat : ℤ)) hlow', smul_zero]
          have hr0 : (hdec.decompose' (r : S) 0 : S) = 0 := by
            have h := DirectSum.decompose_of_mem_ne (ringModuleComponent G)
              r.property hi0
            change (hdec.decompose' (r : S) 0 : S) = 0 at h
            exact h
          rw [hr0, zero_smul]

private lemma graded_finite_homogeneous_generators_submodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N' : Submodule S M) (hN' : IsGradedSubmodule G 𝓜 N')
    [Module.Finite S N'] :
    ∃ (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M),
      (∀ i, x i ∈ 𝓜.component (d i) ∧ x i ∈ N') ∧
        Submodule.span S (Set.range x) = N' := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := N')
  let ι := Σ i : Fin n, (DirectSum.decompose 𝓜.component (s i : M)).support
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let d : Fin (Fintype.card ι) → ℤ := fun k => (e.symm k).2
  let x : Fin (Fintype.card ι) → M := fun k =>
    (DirectSum.decompose 𝓜.component (s (e.symm k).1 : M) (e.symm k).2 : M)
  refine ⟨Fintype.card ι, d, x, ?_, ?_⟩
  · intro k
    constructor
    · exact (DirectSum.decompose 𝓜.component
        (s (e.symm k).1 : M) (e.symm k).2).property
    · exact hN' _ (s (e.symm k).1).property
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      exact (hN' _ (s (e.symm i).1).property)
    · intro z hz
      let z' : N' := ⟨z, hz⟩
      have hzspan : z' ∈ Submodule.span S (Set.range s) := by
        rw [hs]
        trivial
      refine Submodule.span_induction
        (p := fun (y : N') _ => (y : M) ∈ Submodule.span S (Set.range x))
        ?_ ?_ ?_ ?_ hzspan
      · rintro y ⟨i, rfl⟩
        rw [← DirectSum.sum_support_decompose 𝓜.component (s i : M)]
        apply Submodule.sum_mem
        intro j hj
        apply Submodule.subset_span
        refine ⟨e ⟨i, ⟨j, hj⟩⟩, ?_⟩
        dsimp [x]
        rw [e.symm_apply_apply]
      · simp
      · intro y z _ _ hy hz
        exact add_mem hy hz
      · intro a y _ hy
        change a • (y : M) ∈ Submodule.span S (Set.range x)
        exact Submodule.smul_mem _ a hy

theorem graded_nakayama_zero
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Module.Finite S M]
    (hM : irrelevantIdeal G • (⊤ : Submodule S M) = ⊤) :
    (⊤ : Submodule S M) = ⊥ := by
  classical
  obtain ⟨n, d, x, hx, hspan⟩ :=
    graded_finite_homogeneous_generators G 𝓜
  have hxi_zero : ∀ i, x i = 0 := by
    intro i
    by_contra hxi
    let t : Finset ℤ :=
      (Finset.univ.filter (fun j : Fin n => x j ≠ 0)).image d
    have ht : t.Nonempty := by
      refine ⟨d i, ?_⟩
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, rfl⟩
    let k : ℤ := t.min' ht
    have hk : ∀ j, x j ≠ 0 → k ≤ d j := by
      intro j hj
      exact Finset.min'_le t (d j)
        (Finset.mem_image.mpr ⟨j,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
    obtain ⟨j, hj, hjk⟩ :=
      Finset.mem_image.mp (Finset.min'_mem t ht)
    have hj0 : x j ≠ 0 := (Finset.mem_filter.mp hj).2
    have hlow := graded_lower_components_zero G 𝓜 k n d x hx hk hspan
    let hdec : DirectSum.Decomposition (ringModuleComponent G) :=
      Classical.choice (ringModule_decomposition_exists G)
    have hformula := graded_smul_component_formula G 𝓜 k hdec hlow
    have hjzero : (DirectSum.decompose 𝓜.component (x j) k : M) = 0 := by
      have hjmem : x j ∈ irrelevantIdeal G • (⊤ : Submodule S M) := by
        rw [hM]
        trivial
      refine Submodule.smul_induction_on hjmem ?_ ?_
      · intro r hr y hy
        have hr' : r ∈ HomogeneousIdeal.irrelevant G.component := hr
        have hr0G : (DirectSum.decompose G.component r 0 : S) = 0 := by
          have h :=
            (HomogeneousIdeal.mem_irrelevant_iff
              (𝒜 := G.component) r).mp hr'
          simpa only [GradedRing.proj_apply] using h
        have hr0 : (hdec.decompose' r 0 : S) = 0 := by
          rw [ringModule_zero_component_eq G hdec r]
          exact hr0G
        have h := hformula r y
        rw [h, hr0, zero_smul]
      · intro u v hu hv
        have hdecomp_add (u v : M) :
            DirectSum.decompose 𝓜.component (u + v) =
              DirectSum.decompose 𝓜.component u +
                DirectSum.decompose 𝓜.component v :=
          (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
        rw [hdecomp_add]
        change (DirectSum.decompose 𝓜.component u k : M) +
            (DirectSum.decompose 𝓜.component v k : M) = 0
        rw [hu, hv, add_zero]
    have hkj : k = d j := hjk.symm
    rw [hkj, DirectSum.decompose_of_mem_same 𝓜.component (hx j)] at hjzero
    exact hj0 hjzero
  rw [← hspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    rw [hxi_zero i]
    exact Submodule.zero_mem _
  · exact bot_le

private lemma graded_lower_components_in_submodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N N' : Submodule S M) (hN : IsGradedSubmodule G 𝓜 N)
    (k : ℤ) (n : ℕ) (d : Fin n → ℤ) (x : Fin n → M)
    (hx : ∀ i, x i ∈ 𝓜.component (d i) ∧ x i ∈ N')
    (hk : ∀ i, x i ∉ N → k ≤ d i)
    (hspan : Submodule.span S (Set.range x) = N') :
    ∀ (y : M), y ∈ N' → ∀ (e : ℤ), e < k →
      (DirectSum.decompose 𝓜.component y e : M) ∈ N := by
  let 𝓡 := ringAsGradedModule G
  let _ : DirectSum.Decomposition (ringModuleComponent G) := 𝓡.decomposition
  intro y hy
  rw [← hspan] at hy
  have hdecomp_add (u v : M) :
      DirectSum.decompose 𝓜.component (u + v) =
        DirectSum.decompose 𝓜.component u +
          DirectSum.decompose 𝓜.component v :=
    (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
  refine Submodule.span_induction (p := fun y _ => ∀ e : ℤ, e < k →
      (DirectSum.decompose 𝓜.component y e : M) ∈ N) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨i, rfl⟩ e he
    by_cases hzi : x i ∈ N
    · exact hN e hzi
    · exact DirectSum.decompose_of_mem_ne 𝓜.component (hx i).1
        (ne_of_gt (lt_of_lt_of_le he (hk i hzi))) ▸ N.zero_mem
  · intro e he
    simp
  · intro y z _ _ hy hz e he
    rw [hdecomp_add]
    change (DirectSum.decompose 𝓜.component y e : M) +
        (DirectSum.decompose 𝓜.component z e : M) ∈ N
    exact N.add_mem (hy e he) (hz e he)
  · intro a y _ hy e he
    induction a using DirectSum.Decomposition.inductionOn
        (ℳ := ringModuleComponent G) with
    | zero => simp
    | add a b ha hb =>
        rw [add_smul, hdecomp_add]
        change (DirectSum.decompose 𝓜.component (a • y) e : M) +
            (DirectSum.decompose 𝓜.component (b • y) e : M) ∈ N
        exact N.add_mem ha hb
    | @homogeneous i a =>
        by_cases hi : i < 0
        · have ha0 : (a : S) = 0 := by
            have ha' : (a : S) ∈ (⊥ : AddSubgroup S) := by
              rw [← ringModuleComponent_of_negative G hi]
              exact a.property
            simpa using ha'
          simp [ha0]
        · have hi' : 0 ≤ i := le_of_not_gt hi
          have ha' : (a : S) ∈ G.component i.toNat := by
            rw [← ringModuleComponent_of_nonnegative G hi']
            exact a.property
          have hproj : ∀ e : ℤ, ∀ z : M,
              (DirectSum.decompose 𝓜.component ((a : S) • z) e : M) =
                (a : S) •
                  (DirectSum.decompose 𝓜.component z
                    (e - (i.toNat : ℤ)) : M) := by
            intro e z
            induction z using DirectSum.Decomposition.inductionOn
                (ℳ := 𝓜.component) with
            | zero => simp
            | add z w hz hw =>
                rw [smul_add, hdecomp_add ((a : S) • z) ((a : S) • w),
                  hdecomp_add z w]
                change (DirectSum.decompose 𝓜.component ((a : S) • z) e : M) +
                    (DirectSum.decompose 𝓜.component ((a : S) • w) e : M) =
                  (a : S) •
                    ((DirectSum.decompose 𝓜.component z
                        (e - (i.toNat : ℤ)) : M) +
                      (DirectSum.decompose 𝓜.component w
                        (e - (i.toNat : ℤ)) : M))
                rw [hz, hw, smul_add]
            | @homogeneous j z =>
                have hmul := 𝓜.gradedSMul.smul_mem ha' z.property
                have hmul' : (a : S) • (z : M) ∈
                    𝓜.component ((i.toNat : ℤ) + j) := by
                  change (a : S) • (z : M) ∈
                    𝓜.component ((i.toNat : ℤ) + j) at hmul
                  exact hmul
                by_cases hdeg : (i.toNat : ℤ) + j = e
                · have hjeq : (i.toNat : ℤ) + j - (i.toNat : ℤ) = j := by omega
                  rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component hmul',
                    hjeq, DirectSum.decompose_of_mem_same 𝓜.component z.property]
                · have hjeq : j ≠ e - (i.toNat : ℤ) := by omega
                  rw [DirectSum.decompose_of_mem_ne 𝓜.component hmul' hdeg,
                    DirectSum.decompose_of_mem_ne 𝓜.component z.property hjeq]
                  simp
          rw [hproj e y]
          have hlow : e - (i.toNat : ℤ) < k := by
            have hnonneg : 0 ≤ (i.toNat : ℤ) := Int.natCast_nonneg _
            omega
          exact N.smul_mem (a : S) (hy (e - (i.toNat : ℤ)) hlow)

private lemma graded_smul_component_submodule_formula
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N N' : Submodule S M) (k : ℤ)
    (hdec : DirectSum.Decomposition (ringModuleComponent G))
    (hlow : ∀ (y : M), y ∈ N' → ∀ (e : ℤ), e < k →
      (DirectSum.decompose 𝓜.component y e : M) ∈ N) :
    ∀ (r : S) (y : M), y ∈ N' →
      (DirectSum.decompose 𝓜.component (r • y) k : M) -
          (DirectSum.decompose G.component r 0 : S) •
            (DirectSum.decompose 𝓜.component y k : M) ∈ N := by
  let _ : DirectSum.Decomposition (ringModuleComponent G) := hdec
  have hdecomp_add (u v : M) :
      DirectSum.decompose 𝓜.component (u + v) =
        DirectSum.decompose 𝓜.component u +
          DirectSum.decompose 𝓜.component v :=
    (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
  have hhom : ∀ (i : ℤ) (a : ringModuleComponent G i), 0 ≤ i → ∀ y : M,
      (DirectSum.decompose 𝓜.component ((a : S) • y) k : M) =
        (a : S) •
          (DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) := by
    intro i a hi y
    have ha : (a : S) ∈ G.component i.toNat := by
      rw [← ringModuleComponent_of_nonnegative G hi]
      exact a.property
    induction y using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp
    | add y z hy hz =>
        rw [smul_add, hdecomp_add ((a : S) • y) ((a : S) • z),
          hdecomp_add y z]
        change (DirectSum.decompose 𝓜.component ((a : S) • y) k : M) +
            (DirectSum.decompose 𝓜.component ((a : S) • z) k : M) =
          (a : S) •
            ((DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) +
              (DirectSum.decompose 𝓜.component z (k - (i.toNat : ℤ)) : M))
        rw [hy, hz, smul_add]
    | @homogeneous j y =>
        have hmul := 𝓜.gradedSMul.smul_mem ha y.property
        have hmul' : (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) := by
          change (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) at hmul
          exact hmul
        by_cases hdeg : (i.toNat : ℤ) + j = k
        · have hjeq : (i.toNat : ℤ) + j - (i.toNat : ℤ) = j := by omega
          rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component hmul',
            hjeq, DirectSum.decompose_of_mem_same 𝓜.component y.property]
        · have hjeq : j ≠ k - (i.toNat : ℤ) := by omega
          rw [DirectSum.decompose_of_mem_ne 𝓜.component hmul' hdeg,
            DirectSum.decompose_of_mem_ne 𝓜.component y.property hjeq]
          simp
  have hrdecomp_add (r s : S) :
      hdec.decompose' (r + s) = hdec.decompose' r + hdec.decompose' s :=
    (DirectSum.decomposeAddEquiv (ringModuleComponent G)).map_add r s
  have hrGdecomp_add (r s : S) :
      DirectSum.decompose G.component (r + s) =
        DirectSum.decompose G.component r + DirectSum.decompose G.component s :=
    (DirectSum.decomposeAddEquiv G.component).map_add r s
  intro r y hy
  induction r using DirectSum.Decomposition.inductionOn
      (ℳ := ringModuleComponent G) with
  | zero => simp
  | add r s hr hs =>
      rw [add_smul, hdecomp_add ((r : S) • y) ((s : S) • y),
        hrGdecomp_add]
      change
        ((DirectSum.decompose 𝓜.component (r • y) k : M) +
            (DirectSum.decompose 𝓜.component (s • y) k : M)) -
            ((DirectSum.decompose G.component r 0 : S) +
              (DirectSum.decompose G.component s 0 : S)) •
              (DirectSum.decompose 𝓜.component y k : M) ∈ N
      rw [add_smul]
      simpa [sub_add_sub_comm] using N.add_mem hr hs
  | @homogeneous i r =>
      by_cases hi : i < 0
      · have hr0 : (r : S) = 0 := by
          have hr' : (r : S) ∈ (⊥ : AddSubgroup S) := by
            rw [← ringModuleComponent_of_negative G hi]
            exact r.property
          simpa using hr'
        simp [hr0]
      · by_cases hi0 : i = 0
        · subst i
          have hr0 : (DirectSum.decompose G.component (r : S) 0 : S) = (r : S) := by
            exact DirectSum.decompose_of_mem_same G.component r.property
          have hm := hhom 0 r (by rfl) y
          rw [hr0]
          have hzero : k - (Int.toNat (0 : ℤ) : ℤ) = k := by omega
          rw [hzero] at hm
          rw [hm]
          simp
        · have hi' : 0 < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hi0)
          have hm := hhom i r (le_of_lt hi') y
          have hnat : i.toNat ≠ 0 := by omega
          have hr0 : (DirectSum.decompose G.component (r : S) 0 : S) = 0 := by
            rw [DirectSum.decompose_of_mem_ne G.component
              (by simpa [ringModuleComponent, le_of_lt hi'] using r.property) hnat]
          rw [hm, hr0, zero_smul, sub_zero]
          have hlow' : k - (i.toNat : ℤ) < k := by
            have hnonneg : 0 ≤ (i.toNat : ℤ) := Int.natCast_nonneg _
            omega
          exact N.smul_mem (r : S) (hlow y hy (k - (i.toNat : ℤ)) hlow')

theorem graded_nakayama_submodule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (N N' : Submodule S M)
    (hN : IsGradedSubmodule G 𝓜 N) (hN' : IsGradedSubmodule G 𝓜 N')
    [Module.Finite S N']
    (hM : (⊤ : Submodule S M) = N ⊔ irrelevantIdeal G • N') :
    N = ⊤ := by
  classical
  obtain ⟨n, d, x, hx, hspan⟩ :=
    graded_finite_homogeneous_generators_submodule G 𝓜 N' hN'
  have hgenN : ∀ i, x i ∈ N := by
    intro i
    by_contra hxi
    let t : Finset ℤ :=
      (Finset.univ.filter (fun j : Fin n => x j ∉ N)).image d
    have ht : t.Nonempty := by
      refine ⟨d i, ?_⟩
      exact Finset.mem_image.mpr ⟨i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩, rfl⟩
    let k : ℤ := t.min' ht
    have hk : ∀ j, x j ∉ N → k ≤ d j := by
      intro j hj
      exact Finset.min'_le t (d j)
        (Finset.mem_image.mpr ⟨j,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
    obtain ⟨j, hj, hjk⟩ :=
      Finset.mem_image.mp (Finset.min'_mem t ht)
    have hj0 : x j ∉ N := (Finset.mem_filter.mp hj).2
    have hlow := graded_lower_components_in_submodule G 𝓜 N N' hN
      k n d x hx hk hspan
    let hdec : DirectSum.Decomposition (ringModuleComponent G) :=
      Classical.choice (ringModule_decomposition_exists G)
    have hformula := graded_smul_component_submodule_formula
      G 𝓜 N N' k hdec hlow
    have hjcomp :
        (DirectSum.decompose 𝓜.component (x j) k : M) ∈ N := by
      have hjmem : x j ∈ N ⊔ irrelevantIdeal G • N' := by
        rw [← hM]
        trivial
      rcases Submodule.mem_sup.mp hjmem with ⟨u, hu, v, hv, huv⟩
      have hdecomp_add (u v : M) :
          DirectSum.decompose 𝓜.component (u + v) =
            DirectSum.decompose 𝓜.component u +
              DirectSum.decompose 𝓜.component v :=
        (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
      rw [← huv, hdecomp_add]
      change (DirectSum.decompose 𝓜.component u k : M) +
          (DirectSum.decompose 𝓜.component v k : M) ∈ N
      apply N.add_mem
      · exact hN k hu
      · refine Submodule.smul_induction_on hv ?_ ?_
        · intro r hr y hy
          have hr' : r ∈ HomogeneousIdeal.irrelevant G.component := hr
          have hr0 : (DirectSum.decompose G.component r 0 : S) = 0 := by
            have h :=
              (HomogeneousIdeal.mem_irrelevant_iff
                (𝒜 := G.component) r).mp hr'
            simpa only [GradedRing.proj_apply] using h
          have h := hformula r y hy
          rw [hr0, zero_smul, sub_zero] at h
          exact h
        · intro u v hu hv
          rw [hdecomp_add]
          change (DirectSum.decompose 𝓜.component u k : M) +
              (DirectSum.decompose 𝓜.component v k : M) ∈ N
          exact N.add_mem hu hv
    have hkj : k = d j := hjk.symm
    rw [hkj, DirectSum.decompose_of_mem_same 𝓜.component (hx j).1] at hjcomp
    exact hj0 hjcomp
  have hN'le : N' ≤ N := by
    rw [← hspan]
    exact Submodule.span_le.2 (by
      rintro z ⟨i, rfl⟩
      exact hgenN i)
  have hIsub : irrelevantIdeal G • N' ≤ N := by
    refine Submodule.smul_le.2 ?_
    intro r hr y hy
    exact N.smul_mem r (hN'le hy)
  apply top_unique
  rw [hM]
  exact sup_le le_rfl hIsub

theorem graded_nakayama_surjective
    (G : GradedRingData S) (𝓝 : GradedModuleData G N) (𝓜 : GradedModuleData G M)
    (f : N →ₗ[S] M) (hf : IsGradedLinearMap G 𝓝 𝓜 f)
    [Module.Finite S M]
    (hquot : Function.Surjective
      ((irrelevantIdeal G • (⊤ : Submodule S M)).mkQ.comp f)) :
    Function.Surjective f := by
  let I : Submodule S M := irrelevantIdeal G • (⊤ : Submodule S M)
  have hmap (y : N) (d : ℤ) :
      (DirectSum.decompose 𝓜.component (f y) d : M) =
        f (DirectSum.decompose 𝓝.component y d : N) := by
    induction y using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓝.component) with
    | zero => simp
    | add y z hy hz =>
        rw [map_add, DirectSum.decompose_add, DirectSum.add_apply]
        change
          ((DirectSum.decompose 𝓜.component (f y) d : M) +
            (DirectSum.decompose 𝓜.component (f z) d : M)) =
          f (DirectSum.decompose 𝓝.component (y + z) d : N)
        rw [DirectSum.decompose_add, DirectSum.add_apply]
        change
          ((DirectSum.decompose 𝓜.component (f y) d : M) +
            (DirectSum.decompose 𝓜.component (f z) d : M)) =
          f ((DirectSum.decompose 𝓝.component y d : N) +
            (DirectSum.decompose 𝓝.component z d : N))
        rw [hy, hz, map_add]
    | @homogeneous d' y =>
        by_cases hdeg : d' = d
        · subst d'
          rw [DirectSum.decompose_of_mem_same 𝓝.component y.property,
            DirectSum.decompose_of_mem_same 𝓜.component (hf d y y.property)]
        · rw [DirectSum.decompose_of_mem_ne 𝓝.component y.property hdeg,
            DirectSum.decompose_of_mem_ne 𝓜.component (hf d' y y.property) hdeg]
          simp
  have hN : IsGradedSubmodule G 𝓜 (LinearMap.range f) := by
    change ∀ (d : ℤ) ⦃y : M⦄, y ∈ LinearMap.range f →
      (DirectSum.decompose 𝓜.component y d : M) ∈ LinearMap.range f
    intro d y hy
    rcases hy with ⟨z, rfl⟩
    rw [hmap]
    exact ⟨DirectSum.decompose 𝓝.component z d, rfl⟩
  have htop : IsGradedSubmodule G 𝓜 (⊤ : Submodule S M) := by
    intro d y hy
    trivial
  have hM : (⊤ : Submodule S M) = LinearMap.range f ⊔ I := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz⟩ := hquot (I.mkQ y)
      change I.mkQ (f z) = I.mkQ y at hz
      have hzero : I.mkQ (y - f z) = 0 := by
        rw [map_sub, hz]
        exact sub_self _
      have hmem : y - f z ∈ I := by
        change Submodule.Quotient.mk (y - f z) = 0 at hzero
        exact (Submodule.Quotient.mk_eq_zero I).mp hzero
      refine Submodule.mem_sup.mpr ⟨f z, ⟨z, rfl⟩, y - f z, hmem, ?_⟩
      abel
    · exact sup_le le_top le_top
  have hrange : LinearMap.range f = (⊤ : Submodule S M) :=
    graded_nakayama_submodule G 𝓜 (LinearMap.range f) ⊤ hN htop hM
  exact LinearMap.range_eq_top.mp hrange

theorem graded_nakayama_generators
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Module.Finite S M] (n : ℕ) (x : Fin n → M)
    (hx : ∃ d : Fin n → ℤ,
      (∀ i, x i ∈ 𝓜.component (d i)) ∧
        Submodule.span S
          (Set.range (fun i =>
            (irrelevantIdeal G • (⊤ : Submodule S M)).mkQ (x i))) = ⊤) :
    Submodule.span S (Set.range x) = ⊤ := by
  classical
  rcases hx with ⟨d, hxd, hquot⟩
  let I : Submodule S M := irrelevantIdeal G • (⊤ : Submodule S M)
  let P : Submodule S M := Submodule.span S (Set.range x)
  let _ : DirectSum.Decomposition (ringModuleComponent G) :=
    (ringAsGradedModule G).decomposition
  have hproj : ∀ (i : ℤ) (a : ringModuleComponent G i), 0 ≤ i →
      ∀ (k : ℤ) (y : M),
        (DirectSum.decompose 𝓜.component ((a : S) • y) k : M) =
          (a : S) •
            (DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) := by
    intro i a hi k y
    have ha : (a : S) ∈ G.component i.toNat := by
      rw [← ringModuleComponent_of_nonnegative G hi]
      exact a.property
    induction y using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp
    | add y z hy hz =>
        rw [smul_add, DirectSum.decompose_add, DirectSum.add_apply]
        rw [DirectSum.decompose_add, DirectSum.add_apply]
        change
          ((DirectSum.decompose 𝓜.component ((a : S) • y) k : M) +
            (DirectSum.decompose 𝓜.component ((a : S) • z) k : M)) =
          (a : S) •
            ((DirectSum.decompose 𝓜.component y (k - (i.toNat : ℤ)) : M) +
              (DirectSum.decompose 𝓜.component z (k - (i.toNat : ℤ)) : M))
        rw [hy, hz, smul_add]
    | @homogeneous j y =>
        have hmul := 𝓜.gradedSMul.smul_mem ha y.property
        have hmul' : (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) := by
          change (a : S) • (y : M) ∈
            𝓜.component ((i.toNat : ℤ) + j) at hmul
          exact hmul
        by_cases hdeg : (i.toNat : ℤ) + j = k
        · have hjeq : (i.toNat : ℤ) + j - (i.toNat : ℤ) = j := by omega
          rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component hmul',
            hjeq, DirectSum.decompose_of_mem_same 𝓜.component y.property]
        · have hjeq : j ≠ k - (i.toNat : ℤ) := by omega
          rw [DirectSum.decompose_of_mem_ne 𝓜.component hmul' hdeg,
            DirectSum.decompose_of_mem_ne 𝓜.component y.property hjeq]
          simp
  have hspan_homogeneous : ∀ (y : M), y ∈ P → ∀ k : ℤ,
      (DirectSum.decompose 𝓜.component y k : M) ∈ P := by
    intro y hy
    refine Submodule.span_induction (p := fun y _ => ∀ k : ℤ,
        (DirectSum.decompose 𝓜.component y k : M) ∈ P) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨i, rfl⟩ k
      by_cases hdeg : d i = k
      · rw [← hdeg, DirectSum.decompose_of_mem_same 𝓜.component (hxd i)]
        exact Submodule.subset_span ⟨i, rfl⟩
      · rw [DirectSum.decompose_of_mem_ne 𝓜.component (hxd i) hdeg]
        exact P.zero_mem
    · intro k
      simp
    · intro y z _ _ hy hz k
      rw [DirectSum.decompose_add, DirectSum.add_apply]
      change
        (DirectSum.decompose 𝓜.component y k : M) +
            (DirectSum.decompose 𝓜.component z k : M) ∈ P
      exact P.add_mem (hy k) (hz k)
    · intro a y _ hy k
      induction a using DirectSum.Decomposition.inductionOn
          (ℳ := ringModuleComponent G) with
      | zero => simp
      | add a b ha hb =>
          rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply]
          change
            (DirectSum.decompose 𝓜.component (a • y) k : M) +
                (DirectSum.decompose 𝓜.component (b • y) k : M) ∈ P
          exact P.add_mem ha hb
      | @homogeneous i a =>
          by_cases hi : i < 0
          · have ha0 : (a : S) = 0 := by
              have ha' : (a : S) ∈ (⊥ : AddSubgroup S) := by
                rw [← ringModuleComponent_of_negative G hi]
                exact a.property
              simpa using ha'
            simp [ha0]
          · have hi' : 0 ≤ i := le_of_not_gt hi
            rw [hproj i a hi' k y]
            exact P.smul_mem (a : S) (hy (k - (i.toNat : ℤ)))
  have hN : IsGradedSubmodule G 𝓜 P := by
    change ∀ (k : ℤ) ⦃y : M⦄, y ∈ P →
      (DirectSum.decompose 𝓜.component y k : M) ∈ P
    intro k y hy
    exact hspan_homogeneous y hy k
  have htop : IsGradedSubmodule G 𝓜 (⊤ : Submodule S M) := by
    intro k y hy
    trivial
  have hmaptop : Submodule.map I.mkQ P = (⊤ : Submodule S (M ⧸ I)) := by
    rw [Submodule.map_span]
    have hset : I.mkQ '' Set.range x =
        Set.range (fun i => I.mkQ (x i)) := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
    rw [hset]
    simpa [I] using hquot
  have hsup : I ⊔ P = (⊤ : Submodule S M) :=
    (Submodule.map_mkQ_eq_top I P).mp hmaptop
  have hM : (⊤ : Submodule S M) = P ⊔ I := by
    simpa [sup_comm] using hsup.symm
  exact graded_nakayama_submodule G 𝓜 P ⊤ hN htop hM

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
  let _ : AddAction ℕ ℤ :=
    { vadd := fun n m => (n : ℤ) + m
      add_vadd := by
        intro n m z
        change ((n + m : ℕ) : ℤ) + z = (n : ℤ) + ((m : ℤ) + z)
        simp only [Int.natCast_add, add_assoc]
      zero_vadd := by
        intro z
        change (0 : ℤ) + z = z
        exact zero_add z }
  let _ : SetLike.GradedSMul
      (fun n : ℕ => G.component (n * d))
      (fun n : ℤ => 𝓜.component (n * (d : ℤ))) :=
    { smul_mem := by
        intro i j a x ha hx
        have h := 𝓜.gradedSMul.smul_mem ha hx
        change a • x ∈ 𝓜.component ((i + (j : ℤ)) * (d : ℤ))
        change a • x ∈ 𝓜.component ((i * d : ℕ) + (j * (d : ℤ))) at h
        simpa [Nat.cast_mul, add_mul] using h }
  exact ⟨SetLike.gmodule
    (fun n : ℕ => G.component (n * d))
    (fun n : ℤ => 𝓜.component (n * (d : ℤ)))⟩

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
  classical
  obtain ⟨F, hF⟩ := hS.out
  let ι₀ := Σ (x : F), (DirectSum.decompose G.component (x : S)).support
  let x₀ : ι₀ → S := fun i =>
    (DirectSum.decompose G.component (i.1 : S) i.2 : S)
  let s : Finset S :=
    (Finset.univ.image x₀).filter (fun z => ∃ n ≠ 0, z ∈ G.component n)
  have hsgen : Algebra.adjoin (degreeZeroSubring G) (s : Set S) = ⊤ := by
    apply top_unique
    rw [← hF]
    apply Algebra.adjoin_le
    intro z hz
    rw [← DirectSum.sum_support_decompose G.component (z : S)]
    apply (Algebra.adjoin (degreeZeroSubring G) (s : Set S)).sum_mem
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      have hz0 : (DirectSum.decompose G.component (z : S) 0 : S) ∈
          degreeZeroSubring G :=
        (DirectSum.decompose G.component (z : S) 0).property
      exact (Algebra.adjoin (degreeZeroSubring G) (s : Set S)).algebraMap_mem
        ⟨_, hz0⟩
    · have hmem : x₀ ⟨⟨z, hz⟩, ⟨n, hn⟩⟩ ∈ s := by
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_image.mpr
            ⟨⟨⟨z, hz⟩, ⟨n, hn⟩⟩, Finset.mem_univ _, rfl⟩
        · exact ⟨n, hn0, (DirectSum.decompose G.component (z : S) n).property⟩
      exact Algebra.subset_adjoin hmem
  have hshom : ∀ i : s, ∃ n : ℕ, n ≠ 0 ∧
      (i : S) ∈ G.component n := by
    intro i
    exact (Finset.mem_filter.mp i.2).2
  have hq : ∀ i : s, ∃ n : ℕ, n ≠ 0 ∧
      (i : S) ∈ G.component n := by
    intro i
    exact hshom i
  choose q hq0 hqmem using hq
  let r : ℕ := s.card + 1
  let m : ℕ := ∏ i : s, q i
  let monomial : (s → ℕ) → S := fun e =>
    ∏ i : s, (i : S) ^ e i
  let deg : (s → ℕ) → ℕ := fun e => ∑ i : s, q i * e i
  let Q : Submodule (degreeZeroSubring G) S :=
    Submodule.span (degreeZeroSubring G) (Set.range monomial)
  have hmpos : 0 < m := by
    dsimp [m]
    exact Finset.prod_pos (fun i _ => Nat.pos_of_ne_zero (hq0 i))
  have hmono (e : s → ℕ) :
      monomial e ∈ G.component (deg e) := by
    dsimp [monomial, deg]
    simpa [mul_comm] using
      (SetLike.prod_pow_mem_graded G.component q (fun i : s => (i : S)) e
        (F := Finset.univ) (by
          intro i hi
          exact hqmem i))
  have hqdiv (i : s) : q i ∣ m := by
    dsimp [m]
    exact Finset.dvd_prod_of_mem (fun j : s => q j) (Finset.mem_univ i)
  have hextract (E : s → ℕ) (hE : r * m ≤ deg E) :
      ∃ i : s, ∃ c : ℕ, m = q i * c ∧ c ≤ E i := by
    by_cases h : ∃ i : s, m ≤ q i * E i
    · rcases h with ⟨i, hi⟩
      rcases hqdiv i with ⟨c, hc⟩
      refine ⟨i, c, hc, ?_⟩
      apply le_of_mul_le_mul_left
        (show q i * c ≤ q i * E i by simpa [hc] using hi)
      exact Nat.pos_of_ne_zero (hq0 i)
    · have hlt : ∀ i : s, q i * E i < m := by
        intro i
        exact lt_of_not_ge (fun hi => h ⟨i, hi⟩)
      have hsum : deg E ≤ s.card * (m - 1) := by
        dsimp [deg]
        calc
          _ ≤ ∑ i : s, (m - 1) := by
            exact Finset.sum_le_sum (fun i _ => Nat.le_pred_of_lt (hlt i))
          _ = s.card * (m - 1) := by simp
      have hbound : s.card * (m - 1) < r * m := by
        dsimp [r]
        calc
          _ ≤ s.card * m := by
            have hsub : m - 1 < m := Nat.sub_lt hmpos (by omega)
            exact Nat.mul_le_mul_left _ hsub.le
          _ < s.card * m + m := by omega
          _ = (s.card + 1) * m := by simp [Nat.add_mul]
      omega
  have hdeg_add (E F : s → ℕ) :
      deg (fun i => E i + F i) = deg E + deg F := by
    dsimp [deg]
    simp [Nat.mul_add, Finset.sum_add_distrib, add_assoc]
  have hsplit (E : s → ℕ) (hE : r * m ≤ deg E) :
      ∃ A B : s → ℕ,
        (∀ i, A i + B i = E i) ∧ deg A = m ∧ deg B = deg E - m := by
    rcases hextract E hE with ⟨i, c, hmc, hci⟩
    let A : s → ℕ := fun j => if j = i then c else 0
    let B : s → ℕ := fun j => E j - A j
    have hAle : ∀ j, A j ≤ E j := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [A] using hci
      · simp [A, hji]
    have hsum : ∀ j, A j + B j = E j := by
      intro j
      exact Nat.add_sub_of_le (hAle j)
    have hdegA : deg A = m := by
      dsimp [deg, A]
      rw [Finset.sum_eq_single_of_mem i (by simp)]
      · simpa using hmc.symm
      · intro j hj hji
        simp [hji]
    have hdegrel : deg E = deg A + deg B := by
      rw [← hdeg_add A B]
      congr 1
      funext j
      exact (hsum j).symm
    refine ⟨A, B, hsum, hdegA, ?_⟩
    omega
  have hfactor (n : ℕ) (hn : 2 ≤ n) (E : s → ℕ)
      (hE : deg E = n * (r * m)) :
      ∃ A B : s → ℕ,
        (∀ i, A i + B i = E i) ∧ deg A = r * m ∧
          deg B = (n - 1) * (r * m) := by
    have haux : ∀ k N : ℕ, ∀ E : s → ℕ,
        k ≤ r → r + k ≤ N → deg E = N * m →
          ∃ A B : s → ℕ,
            (∀ i, A i + B i = E i) ∧ deg A = k * m ∧
              deg B = (N - k) * m := by
      intro k
      induction k with
      | zero =>
          intro N E hk hN hE'
          refine ⟨fun _ => 0, E, ?_, ?_, ?_⟩
          · intro i
            simp
          · simp [deg]
          · simpa using hE'
      | succ k ih =>
          intro N E hk hN hE'
          have hNk : r ≤ N := by omega
          have hsplit' := hsplit E (by
            have hmul : r * m ≤ N * m := Nat.mul_le_mul_right m hNk
            simpa [hE'] using hmul)
          rcases hsplit' with ⟨C, D, hCD, hCdeg, hDdeg⟩
          have hNminus : r + k ≤ N - 1 := by omega
          have hDdeg' : deg D = (N - 1) * m := by
            rw [hDdeg, hE']
            rw [Nat.sub_mul]
            simp
          rcases ih (N - 1) D (Nat.le_of_succ_le hk) hNminus hDdeg' with
            ⟨A, B, hAB, hAdeg, hBdeg⟩
          have hBdeg' : deg B = (N - (k + 1)) * m := by
            simpa [Nat.sub_sub, add_comm] using hBdeg
          let A' : s → ℕ := fun i => C i + A i
          refine ⟨A', B, ?_, ?_, hBdeg'⟩
          · intro i
            dsimp [A']
            calc
              C i + A i + B i = C i + (A i + B i) := by rw [add_assoc]
              _ = C i + D i := by rw [hAB i]
              _ = E i := hCD i
          · dsimp [A']
            rw [hdeg_add, hCdeg, hAdeg]
            rw [Nat.add_mul, Nat.one_mul, add_comm]
    have hnr : 2 * r ≤ n * r := Nat.mul_le_mul_right r hn
    rcases haux r (n * r) E (le_rfl) (by simpa [two_mul] using hnr) (by
      simpa [Nat.mul_assoc] using hE) with ⟨A, B, hAB, hAdeg, hBdeg⟩
    refine ⟨A, B, hAB, hAdeg, ?_⟩
    rw [hBdeg]
    calc
      (n * r - r) * m = (n * r) * m - r * m := by rw [Nat.sub_mul]
      _ = n * (r * m) - r * m := by simp [Nat.mul_assoc]
      _ = (n - 1) * (r * m) := by
        simpa only [one_mul] using (Nat.sub_mul n 1 (r * m)).symm
  have hfactor_mult (t n : ℕ) (ht : t ≠ 0) (hn : 2 ≤ n) (E : s → ℕ)
      (hE : deg E = n * (t * (r * m))) :
      ∃ A B : s → ℕ,
        (∀ i, A i + B i = E i) ∧ deg A = t * (r * m) ∧
          deg B = (n - 1) * (t * (r * m)) := by
    have htpos : 0 < t := Nat.pos_of_ne_zero ht
    have htr : r ≤ t * r := by
      have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
      simpa using (Nat.mul_le_mul_right r ht1)
    have haux : ∀ k N : ℕ, ∀ E : s → ℕ,
        k ≤ t * r → t * r + k ≤ N → deg E = N * m →
          ∃ A B : s → ℕ,
            (∀ i, A i + B i = E i) ∧ deg A = k * m ∧
              deg B = (N - k) * m := by
      intro k
      induction k with
      | zero =>
          intro N E hk hN hE'
          refine ⟨fun _ => 0, E, ?_, ?_, ?_⟩
          · intro i
            simp
          · simp [deg]
          · simpa using hE'
      | succ k ih =>
          intro N E hk hN hE'
          have hNk : r ≤ N := by
            apply le_trans htr
            omega
          have hsplit' := hsplit E (by
            have hmul : r * m ≤ N * m := Nat.mul_le_mul_right m hNk
            simpa [hE'] using hmul)
          rcases hsplit' with ⟨C, D, hCD, hCdeg, hDdeg⟩
          have hNminus : t * r + k ≤ N - 1 := by omega
          have hDdeg' : deg D = (N - 1) * m := by
            rw [hDdeg, hE']
            rw [Nat.sub_mul]
            simp
          rcases ih (N - 1) D (Nat.le_of_succ_le hk) hNminus hDdeg' with
            ⟨A, B, hAB, hAdeg, hBdeg⟩
          have hBdeg' : deg B = (N - (k + 1)) * m := by
            simpa [Nat.sub_sub, add_comm] using hBdeg
          let A' : s → ℕ := fun i => C i + A i
          refine ⟨A', B, ?_, ?_, hBdeg'⟩
          · intro i
            dsimp [A']
            calc
              C i + A i + B i = C i + (A i + B i) := by rw [add_assoc]
              _ = C i + D i := by rw [hAB i]
              _ = E i := hCD i
          · dsimp [A']
            rw [hdeg_add, hCdeg, hAdeg]
            rw [Nat.add_mul, Nat.one_mul, add_comm]
    have hnr : 2 * (t * r) ≤ n * (t * r) := Nat.mul_le_mul_right (t * r) hn
    rcases haux (t * r) (n * (t * r)) E (le_rfl) (by
      simpa only [two_mul] using hnr) (by
      simpa only [Nat.mul_assoc] using hE) with
      ⟨A, B, hAB, hAdeg, hBdeg⟩
    refine ⟨A, B, hAB, ?_, ?_⟩
    · simpa only [Nat.mul_assoc] using hAdeg
    · rw [hBdeg]
      calc
        (n * (t * r) - t * r) * m = n * (t * r * m) - t * r * m := by
          rw [Nat.sub_mul]
          simp only [Nat.mul_assoc]
        _ = n * (t * (r * m)) - t * (r * m) := by
          simp only [Nat.mul_assoc]
        _ = (n - 1) * (t * (r * m)) := by
          simpa only [one_mul] using (Nat.sub_mul n 1 (t * (r * m))).symm
  have hmonmul (e f : s → ℕ) :
      monomial e * monomial f = monomial (fun i => e i + f i) := by
    dsimp [monomial]
    rw [← Finset.prod_mul_distrib]
    congr 1
    funext i
    exact (pow_add (i : S) (e i) (f i)).symm
  have hQmul : ∀ {a b : S}, a ∈ Q → b ∈ Q → a * b ∈ Q := by
    intro a b ha hb
    refine Submodule.span_induction
      (p := fun a _ => ∀ b : S, b ∈ Q → a * b ∈ Q) ?_ ?_ ?_ ?_ ha b hb
    · intro a ha b hb
      rcases ha with ⟨e, rfl⟩
      refine Submodule.span_induction
        (p := fun b _ => monomial e * b ∈ Q) ?_ ?_ ?_ ?_ hb
      · intro b hb
        rcases hb with ⟨f, rfl⟩
        rw [hmonmul]
        exact Submodule.subset_span ⟨fun i => e i + f i, rfl⟩
      · simp
      · intro b c _ _ hb hc
        rw [mul_add]
        exact Q.add_mem hb hc
      · intro t b _ hb
        change monomial e * ((t : S) * b) ∈ Q
        have h := Q.smul_mem t hb
        change (t : S) * (monomial e * b) ∈ Q at h
        convert h using 1 <;> ring
    · simp
    · intro a b _ _ ha hb c hc
      rw [add_mul]
      exact Q.add_mem (ha c hc) (hb c hc)
    · intro t a _ ha b hb
      change ((t : S) * a) * b ∈ Q
      have h := Q.smul_mem t (ha b hb)
      change (t : S) * (a * b) ∈ Q at h
      convert h using 1 <;> ring
  have hsQ : ∀ z : S, z ∈ s → z ∈ Q := by
    intro z hz
    let i : s := ⟨z, hz⟩
    let e : s → ℕ := fun j => if j = i then 1 else 0
    have he : monomial e = z := by
      dsimp [monomial, e]
      rw [Finset.prod_eq_single_of_mem i (by simp) (by
        intro j hj hji
        simp [hji])]
      simp [i]
    rw [← he]
    exact Submodule.subset_span ⟨e, rfl⟩
  have hQtop : Q = (⊤ : Submodule (degreeZeroSubring G) S) := by
    apply top_unique
    intro z hz
    have hz' : z ∈ Algebra.adjoin (degreeZeroSubring G) (s : Set S) := by
      rw [hsgen]
      trivial
    refine Algebra.adjoin_induction (s := (s : Set S))
      (p := fun y _ => y ∈ Q) ?_ ?_ ?_ ?_ hz'
    · intro z hz
      exact hsQ z hz
    · intro t
      change (t : S) ∈ Q
      have h1 : (1 : S) ∈ Q := by
        apply Submodule.subset_span
        exact ⟨fun _ => 0, by simp [monomial]⟩
      have h := Q.smul_mem t h1
      change (t : S) * 1 ∈ Q at h
      simpa using h
    · intro a b _ _ ha hb
      exact Q.add_mem ha hb
    · intro a b _ _ ha hb
      exact hQmul ha hb
  refine ⟨r * m, Nat.mul_pos (by dsimp [r]; omega) hmpos, ?_⟩
  intro d hd hdiv
  let T : Subring (veroneseRing G d) :=
    Subring.closure
      (Set.range (veroneseDegreeZeroMap G d) ∪
        Set.range (veroneseDegreeOneMap G d))
  change T = (⊤ : Subring (veroneseRing G d))
  rcases hdiv with ⟨t, hdt⟩
  have ht : t ≠ 0 := by
    intro ht0
    subst t
    simp at hdt
    omega
  have subtype_cast :
      ∀ {p q : S → Prop} (h : p = q) (x : S) (hp : p x),
        cast (congrArg (fun r : S → Prop => Subtype r) h)
            (⟨x, hp⟩ : Subtype p) = ⟨x, h ▸ hp⟩ := by
    intro p q h x hp
    cases h
    rfl
  have hmonoT : ∀ k : ℕ, ∀ e : s → ℕ, ∀ hdeg : deg e = k * d,
      DirectSum.of _ k ⟨monomial e, by
        simpa only [hdeg] using hmono e⟩ ∈ T := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro e hdeg
        have hmem : monomial e ∈ G.component (k * d) := by
          simpa [hdeg] using hmono e
        by_cases hk0 : k = 0
        · subst k
          have hz : monomial e ∈ degreeZeroSubring G := by
            change monomial e ∈ G.component 0
            simpa only [zero_mul] using hmem
          apply Subring.subset_closure
          exact Or.inl ⟨⟨monomial e, hz⟩, rfl⟩
        · by_cases hk1 : k = 1
          · subst k
            apply Subring.subset_closure
            exact Or.inr ⟨⟨monomial e, by simpa using hmem⟩, rfl⟩
          · have hk2 : 2 ≤ k := by omega
            have he' : deg e = k * (t * (r * m)) := by
              calc
                deg e = k * d := hdeg
                _ = k * ((r * m) * t) := by rw [hdt]
                _ = k * (t * (r * m)) := by rw [Nat.mul_comm (r * m) t]
            rcases hfactor_mult t k ht hk2 e he' with
              ⟨A, B, hAB, hAdeg, hBdeg⟩
            have hAdeg' : deg A = d := by
              calc
                deg A = t * (r * m) := hAdeg
                _ = (r * m) * t := Nat.mul_comm _ _
                _ = d := hdt.symm
            have hBdeg' : deg B = (k - 1) * d := by
              calc
                deg B = (k - 1) * (t * (r * m)) := hBdeg
                _ = (k - 1) * ((r * m) * t) := by
                  rw [Nat.mul_comm (r * m) t]
                _ = (k - 1) * d := by rw [hdt.symm]
            have hAcomp : monomial A ∈ G.component d := by
              simpa [hAdeg'] using hmono A
            have hBcomp : monomial B ∈ G.component ((k - 1) * d) := by
              simpa [hBdeg'] using hmono B
            have hBin :
                DirectSum.of _ (k - 1) ⟨monomial B, hBcomp⟩ ∈ T :=
              ih (k - 1) (by omega) B hBdeg'
            let a : G.component (1 * d) :=
              ⟨monomial A, by simpa only [one_mul] using hAcomp⟩
            let b : G.component ((k - 1) * d) := ⟨monomial B, hBcomp⟩
            have hAin : DirectSum.of _ 1 a ∈ T := by
              apply Subring.subset_closure
              exact Or.inr ⟨⟨monomial A, by simpa only [one_mul] using hAcomp⟩, rfl⟩
            have hprod : monomial A * monomial B = monomial e := by
              rw [hmonmul]
              congr 1
              funext i
              exact hAB i
            have hindex : 1 + (k - 1) = k := by omega
            have hmem' : monomial e ∈ G.component ((1 + (k - 1)) * d) := by
              simpa only [hindex] using hmem
            have hmul :
                DirectSum.of (fun n : ℕ => G.component (n * d)) 1 a *
                    DirectSum.of (fun n : ℕ => G.component (n * d)) (k - 1) b =
                  DirectSum.of (fun n : ℕ => G.component (n * d)) k
                    ⟨monomial e, hmem⟩ := by
              rw [DirectSum.of_mul_of]
              have hgmul :
                  @GradedMonoid.GMul.mul ℕ
                    (fun n : ℕ => G.component (n * d)) _ _ _ _ a b =
                    (⟨monomial e, hmem'⟩ : G.component ((1 + (k - 1)) * d)) := by
                apply Subtype.ext
                change monomial A * monomial B = monomial e
                exact hprod
              rw [hgmul]
              apply DirectSum.of_eq_of_gradedMonoid_eq
              apply Sigma.ext hindex
              have hset :
                  G.component ((1 + (k - 1)) * d) = G.component (k * d) :=
                congrArg (fun n : ℕ => G.component (n * d)) hindex
              have hset' :
                  (fun x : S => x ∈ G.component ((1 + (k - 1)) * d)) =
                    (fun x : S => x ∈ G.component (k * d)) := by
                exact congrArg
                  (fun H : AddSubgroup S => fun x : S => x ∈ H) hset
              have htypes :
                  (G.component ((1 + (k - 1)) * d) : Type v) =
                    (G.component (k * d) : Type v) := by
                exact congrArg (fun p : S → Prop => Subtype p) hset'
              have hmemA : monomial e ∈ G.component ((1 + (k - 1)) * d) :=
                Eq.mpr (congrFun hset' (monomial e)) hmem
              have hproof :
                  hmem' = hmemA := Subsingleton.elim _ _
              have hcast :
                  cast htypes
                      (⟨monomial e, hmem'⟩ : G.component ((1 + (k - 1)) * d)) =
                    (⟨monomial e, hmem⟩ : G.component (k * d)) := by
                calc
                  cast htypes
                      (⟨monomial e, hmem'⟩ : G.component ((1 + (k - 1)) * d)) =
                      cast htypes
                        (⟨monomial e, hmemA⟩ :
                          G.component ((1 + (k - 1)) * d)) := by rw [hproof]
                  _ = ⟨monomial e, Eq.mp (congrFun hset' (monomial e)) hmemA⟩ :=
                    subtype_cast hset' (monomial e) hmemA
                  _ = ⟨monomial e, hmem⟩ := by
                    apply Subtype.ext
                    rfl
              exact heq_of_cast_eq htypes hcast
            rw [← hmul]
            exact T.mul_mem hAin hBin
  let lift : S → ℕ → veroneseRing G d := fun z k =>
    DirectSum.of _ k ⟨(DirectSum.decompose G.component z (k * d) : S),
      (DirectSum.decompose G.component z (k * d)).property⟩
  have hprojT : ∀ z : S, z ∈ Q → ∀ k : ℕ, lift z k ∈ T := by
    intro z hz
    refine Submodule.span_induction
      (p := fun z _ => ∀ k : ℕ, lift z k ∈ T)
      (mem := by
        intro w hw k
        rcases hw with ⟨e, rfl⟩
        by_cases hzero : monomial e = 0
        · simp [lift, hzero]
        · by_cases hdeg : deg e = k * d
          · have h := hmonoT k e hdeg
            change DirectSum.of _ k ⟨
              (DirectSum.decompose G.component (monomial e) (k * d) : S),
              (DirectSum.decompose G.component (monomial e) (k * d)).property⟩ ∈ T
            have hdecomp :
                (DirectSum.decompose G.component (monomial e) (k * d) : S) =
                  monomial e := by
              rw [← hdeg, DirectSum.decompose_of_mem_same G.component (hmono e)]
            have hmem' : monomial e ∈ G.component (k * d) := by
              simpa only [hdeg] using hmono e
            have hsub :
                (⟨(DirectSum.decompose G.component (monomial e) (k * d) : S),
                  (DirectSum.decompose G.component (monomial e) (k * d)).property⟩ :
                    G.component (k * d)) = ⟨monomial e, hmem'⟩ := by
              apply Subtype.ext
              exact hdecomp
            rw [hsub]
            exact h
          · have h := hmono e
            change DirectSum.of _ k ⟨
              (DirectSum.decompose G.component (monomial e) (k * d) : S),
              (DirectSum.decompose G.component (monomial e) (k * d)).property⟩ ∈ T
            have hdecomp :
                (DirectSum.decompose G.component (monomial e) (k * d) : S) = 0 := by
              rw [DirectSum.decompose_of_mem_ne G.component h hdeg]
            have hsub :
                (⟨(DirectSum.decompose G.component (monomial e) (k * d) : S),
                  (DirectSum.decompose G.component (monomial e) (k * d)).property⟩ :
                    G.component (k * d)) = 0 := by
              apply Subtype.ext
              exact hdecomp
            rw [hsub]
            simp)
      (zero := by
        intro k
        simp [lift])
      (add := by
        intro a b _ _ ha hb k
        have h := T.add_mem (ha k) (hb k)
        simpa [lift, DirectSum.decompose_add, DirectSum.add_apply] using h)
      (smul := by
        intro c a _ ha k
        have hc0 : (c : S) ∈ G.component 0 := by
          change (c : S) ∈ G.component 0
          exact c.property
        have hc : (c : S) ∈ G.component (0 * d) := by
          simpa only [zero_mul] using hc0
        have hcT : DirectSum.of _ 0 ⟨(c : S), hc⟩ ∈ T := by
          apply Subring.subset_closure
          exact Or.inl ⟨c, rfl⟩
        have h := T.mul_mem hcT (ha k)
        have hdecomp :=
          DirectSum.coe_decompose_mul_of_left_mem_zero G.component
            (a_mem := hc0) (b := a) (j := k * d)
        change lift ((c : S) * a) k ∈ T
        have hprodmem :
            (c : S) * (DirectSum.decompose G.component a (k * d) : S) ∈
              G.component (k * d) := by
          rw [← hdecomp]
          exact (DirectSum.decompose G.component ((c : S) * a) (k * d)).property
        have hindex0 : 0 + k = k := Nat.zero_add k
        have hset :
            G.component ((0 + k) * d) = G.component (k * d) :=
          congrArg (fun n : ℕ => G.component (n * d)) hindex0
        have hset' :
            (fun x : S => x ∈ G.component ((0 + k) * d)) =
              (fun x : S => x ∈ G.component (k * d)) := by
          exact congrArg
            (fun H : AddSubgroup S => fun x : S => x ∈ H) hset
        have hleftmem :
            (c : S) * (DirectSum.decompose G.component a (k * d) : S) ∈
              G.component ((0 + k) * d) :=
          Eq.mpr (congrFun hset' ((c : S) *
            (DirectSum.decompose G.component a (k * d) : S))) hprodmem
        have hgmul :
            @GradedMonoid.GMul.mul ℕ
                (fun n : ℕ => G.component (n * d)) _ _ _ _
                ⟨(c : S), hc⟩
                ⟨DirectSum.decompose G.component a (k * d),
                  (DirectSum.decompose G.component a (k * d)).property⟩ =
              ⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
                hleftmem⟩ := by
          apply Subtype.ext
          rfl
        rw [DirectSum.of_mul_of, hgmul] at h
        change DirectSum.of (fun n : ℕ => G.component (n * d)) (0 + k)
          ⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
            hleftmem⟩ ∈ T at h
        have hzero :
              DirectSum.of (fun n : ℕ => G.component (n * d)) (0 + k)
                ⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
                  hleftmem⟩ =
              DirectSum.of (fun n : ℕ => G.component (n * d)) k
                ⟨DirectSum.decompose G.component ((c : S) * a) (k * d),
                  (DirectSum.decompose G.component ((c : S) * a) (k * d)).property⟩ := by
          apply DirectSum.of_eq_of_gradedMonoid_eq
          apply Sigma.ext hindex0
          have htypes :
              (G.component ((0 + k) * d) : Type v) =
                (G.component (k * d) : Type v) := by
            exact congrArg (fun p : S → Prop => Subtype p) hset'
          have hcast :
              cast htypes
                  (⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
                    hleftmem⟩ :
                    G.component ((0 + k) * d)) =
                  (⟨DirectSum.decompose G.component ((c : S) * a) (k * d),
                  (DirectSum.decompose G.component ((c : S) * a) (k * d)).property⟩ :
                  G.component (k * d)) := by
            calc
                  cast htypes
                      (⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
                    hleftmem⟩ : G.component ((0 + k) * d)) =
                  ⟨(c : S) * (DirectSum.decompose G.component a (k * d) : S),
                    Eq.mp (congrFun hset' ((c : S) *
                      (DirectSum.decompose G.component a (k * d) : S))) hleftmem⟩ :=
                subtype_cast hset' ((c : S) *
                  (DirectSum.decompose G.component a (k * d) : S)) hleftmem
              _ =
                  ⟨DirectSum.decompose G.component ((c : S) * a) (k * d),
                    (DirectSum.decompose G.component ((c : S) * a) (k * d)).property⟩ := by
                apply Subtype.ext
                exact hdecomp.symm
          exact heq_of_cast_eq htypes hcast
        rw [hzero] at h
        simpa [lift] using h)
      hz
  have hcompT : ∀ k : ℕ, ∀ y : G.component (k * d),
      DirectSum.of _ k y ∈ T := by
    intro k y
    have hyQ : (y : S) ∈ Q := by
      rw [hQtop]
      trivial
    have h := hprojT (y : S) hyQ k
    change DirectSum.of _ k ⟨
      (DirectSum.decompose G.component (y : S) (k * d) : S),
      (DirectSum.decompose G.component (y : S) (k * d)).property⟩ ∈ T at h
    have hdecomp :
        (DirectSum.decompose G.component (y : S) (k * d) : S) = (y : S) :=
      DirectSum.decompose_of_mem_same G.component y.property
    have hsub :
        (⟨(DirectSum.decompose G.component (y : S) (k * d) : S),
          (DirectSum.decompose G.component (y : S) (k * d)).property⟩ :
          G.component (k * d)) = y := by
      apply Subtype.ext
      change (DirectSum.decompose G.component (y : S) (k * d) : S) = (y : S)
      simpa using hdecomp
    rw [hsub] at h
    exact h
  apply top_unique
  intro z hz
  refine DirectSum.induction_on z ?_ ?_ ?_
  · exact T.zero_mem
  · intro k y
    exact hcompT k y
  · intro x y hx hy
    exact T.add_mem hx hy

private theorem exists_finite_homogeneous_ring_generators
    (G : GradedRingData S)
    [Algebra.FiniteType (degreeZeroSubring G) S] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (x : Fin n → S),
      (∀ i, x i ∈ G.component (d i)) ∧
        Algebra.adjoin (degreeZeroSubring G) (Set.range x) = ⊤ := by
  classical
  obtain ⟨F, hF⟩ := (inferInstance : Algebra.FiniteType (degreeZeroSubring G) S).out
  let ι := Σ (z : F), (DirectSum.decompose G.component (z : S)).support
  let _ : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let d : Fin (Fintype.card ι) → ℕ := fun k => (e.symm k).2
  let x : Fin (Fintype.card ι) → S := fun k =>
    (DirectSum.decompose G.component (e.symm k).1 (e.symm k).2 : S)
  refine ⟨Fintype.card ι, d, x, ?_, ?_⟩
  · intro k
    exact (DirectSum.decompose G.component (e.symm k).1 (e.symm k).2).property
  · apply top_unique
    rw [← hF]
    apply Algebra.adjoin_le
    intro z hz
    rw [← DirectSum.sum_support_decompose G.component (z : S)]
    apply (Algebra.adjoin (degreeZeroSubring G) (Set.range x)).sum_mem
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range x)).algebraMap_mem
        ⟨_, (DirectSum.decompose G.component (z : S) 0).property⟩
    · apply Algebra.subset_adjoin
      refine ⟨e ⟨⟨z, hz⟩, ⟨k, hk⟩⟩, ?_⟩
      dsimp [x]
      rw [e.symm_apply_apply]

private theorem graded_component_finite_of_homogeneous_generators
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (r : ℕ) (q : Fin r → ℕ) (a : Fin r → S)
    (ha : ∀ i, a i ∈ G.component (q i))
    (hagen : Algebra.adjoin (degreeZeroSubring G) (Set.range a) = ⊤)
    (m : ℕ) (d : Fin m → ℤ) (x : Fin m → M)
    (hx : ∀ i, x i ∈ 𝓜.component (d i))
    (hxspan : Submodule.span S (Set.range x) = ⊤)
    (n : ℤ) [Module (degreeZeroSubring G) (𝓜.component n)]
    (hsmul : ∀ (c : degreeZeroSubring G) (y : 𝓜.component n),
      ((c • y : 𝓜.component n) : M) = (c : S) • (y : M)) :
    Module.Finite (degreeZeroSubring G) (𝓜.component n) := by
  classical
  let ι := {i : Fin r // 0 < q i}
  let _ : Fintype ι := Fintype.ofFinite ι
  let sp : ι → S := fun i => a i.1
  let qp : ι → ℕ := fun i => q i.1
  have hsp : ∀ i, sp i ∈ G.component (qp i) := by
    intro i
    exact ha i.1
  have hspgen : Algebra.adjoin (degreeZeroSubring G) (Set.range sp) = ⊤ := by
    apply top_unique
    rw [← hagen]
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    by_cases hi : 0 < q i
    · exact Algebra.subset_adjoin ⟨⟨i, hi⟩, rfl⟩
    · have hi0 : q i = 0 := Nat.eq_zero_of_not_pos hi
      have hzi : a i ∈ degreeZeroSubring G := by
        change a i ∈ G.component 0
        simpa [hi0] using ha i
      exact (Algebra.adjoin (degreeZeroSubring G) (Set.range sp)).algebraMap_mem
        ⟨a i, hzi⟩
  let monomial : (ι → ℕ) → S := fun e => ∏ i : ι, (sp i) ^ e i
  let deg : (ι → ℕ) → ℕ := fun e => ∑ i : ι, qp i * e i
  have hmono (e : ι → ℕ) : monomial e ∈ G.component (deg e) := by
    dsimp [monomial, deg]
    simpa [mul_comm] using
      (SetLike.prod_pow_mem_graded G.component qp (fun i : ι => sp i) e
        (F := Finset.univ) (by
          intro i hi
          exact hsp i))
  have hmonmul (e f : ι → ℕ) :
      monomial e * monomial f = monomial (fun i => e i + f i) := by
    dsimp [monomial]
    rw [← Finset.prod_mul_distrib]
    congr 1
    funext i
    exact (pow_add (sp i) (e i) (f i)).symm
  let Q : Submodule (degreeZeroSubring G) S :=
    Submodule.span (degreeZeroSubring G) (Set.range monomial)
  have hQmul : ∀ {u v : S}, u ∈ Q → v ∈ Q → u * v ∈ Q := by
    intro u v hu hv
    refine Submodule.span_induction
      (p := fun u _ => ∀ v : S, v ∈ Q → u * v ∈ Q) ?_ ?_ ?_ ?_ hu v hv
    · intro u hu v hv
      rcases hu with ⟨e, rfl⟩
      refine Submodule.span_induction
        (p := fun v _ => monomial e * v ∈ Q) ?_ ?_ ?_ ?_ hv
      · intro v hv
        rcases hv with ⟨f, rfl⟩
        rw [hmonmul]
        exact Submodule.subset_span ⟨fun i => e i + f i, rfl⟩
      · simp
      · intro v w _ _ hv hw
        rw [mul_add]
        exact Q.add_mem hv hw
      · intro c v _ hv
        change monomial e * ((c : degreeZeroSubring G) * v) ∈ Q
        have h := Q.smul_mem c hv
        change (c : S) * (monomial e * v) ∈ Q at h
        convert h using 1 <;> ring
    · simp
    · intro u v _ _ hu hv w hw
      rw [add_mul]
      exact Q.add_mem (hu w hw) (hv w hw)
    · intro c u _ hu v hv
      change ((c : degreeZeroSubring G) * u) * v ∈ Q
      have h := Q.smul_mem c (hu v hv)
      change (c : S) * (u * v) ∈ Q at h
      convert h using 1 <;> ring
  have hQtop : Q = (⊤ : Submodule (degreeZeroSubring G) S) := by
    apply top_unique
    intro z hz
    have hz' : z ∈ Algebra.adjoin (degreeZeroSubring G) (Set.range sp) := by
      rw [hspgen]
      trivial
    refine Algebra.adjoin_induction (s := Set.range sp)
      (p := fun z _ => z ∈ Q) ?_ ?_ ?_ ?_ hz'
    · intro z hz
      rcases hz with ⟨i, rfl⟩
      let e : ι → ℕ := fun j => if j = i then 1 else 0
      have he : monomial e = sp i := by
        dsimp [monomial, e]
        rw [Finset.prod_eq_single_of_mem i (by simp) (by
          intro j hj hji
          simp [hji])]
        simp
      rw [← he]
      exact Submodule.subset_span ⟨e, rfl⟩
    · intro c
      change (c : S) ∈ Q
      have h1 : (1 : S) ∈ Q := by
        apply Submodule.subset_span
        exact ⟨fun _ => 0, by simp [monomial]⟩
      have h := Q.smul_mem c h1
      change (c : S) * 1 ∈ Q at h
      simpa using h
    · intro u v _ _ hu hv
      exact Q.add_mem hu hv
    · intro u v _ _ hu hv
      exact hQmul hu hv
  let gen : (ι → ℕ) × Fin m → M := fun z => monomial z.1 • x z.2
  let P : Submodule (degreeZeroSubring G) M :=
    Submodule.span (degreeZeroSubring G) (Set.range gen)
  have hP_smul (u : S) (z : M) (hz : z ∈ P) : u • z ∈ P := by
    refine Submodule.span_induction
      (p := fun z _ => u • z ∈ P) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨⟨e, i⟩, rfl⟩
      have hu : u * monomial e ∈ Q := by
        rw [hQtop]
        trivial
      have hmulgen : ∀ v : S, v ∈ Q → v • x i ∈ P := by
        intro v hv
        refine Submodule.span_induction
          (p := fun v _ => v • x i ∈ P) ?_ ?_ ?_ ?_ hv
        · intro v hv
          rcases hv with ⟨f, rfl⟩
          exact Submodule.subset_span ⟨(f, i), rfl⟩
        · simp
        · intro v w _ _ hv hw
          rw [add_smul]
          exact P.add_mem hv hw
        · intro c v _ hv
          have h := P.smul_mem c hv
          convert h using 1
          change ((c : S) * v) • x i = (c : S) • (v • x i)
          rw [smul_smul]
      have h := hmulgen (u * monomial e) hu
      change (u * monomial e) • x i ∈ P at h
      change u • (monomial e • x i) ∈ P
      simpa [smul_smul, smul_eq_mul, mul_assoc] using h
    · simp
    · intro z w _ _ hz hw
      rw [smul_add]
      exact P.add_mem hz hw
    · intro c z _ hz
      have h := P.smul_mem c hz
      convert h using 1
      exact smul_comm u (c : S) z
  let N : Submodule S M :=
    { carrier := P
      zero_mem' := P.zero_mem
      add_mem' := P.add_mem
      smul_mem' := by
        intro u z hz
        exact hP_smul u z hz }
  have hNtop : N = (⊤ : Submodule S M) := by
    apply top_unique
    rw [← hxspan]
    apply Submodule.span_le.2
    rintro z ⟨i, rfl⟩
    exact Submodule.subset_span ⟨((fun _ : ι => 0), i), by simp [gen, monomial]⟩
  let p : Fin m → ℕ := fun i => Int.toNat (n - d i)
  let D := Σ i : Fin m, {e : ι → Fin (p i + 1) //
    ((deg (fun j => (e j : ℕ)) : ℕ) : ℤ) + d i = n}
  let _ : Fintype D := Fintype.ofFinite D
  let cand : D → 𝓜.component n := fun z =>
    ⟨monomial (fun j => (z.2.1 j : ℕ)) • x z.1, by
      have hm := 𝓜.gradedSMul.smul_mem
        (hmono (fun j => (z.2.1 j : ℕ))) (hx z.1)
      change monomial (fun j => (z.2.1 j : ℕ)) • x z.1 ∈
        𝓜.component (((deg (fun j => (z.2.1 j : ℕ)) : ℕ) : ℤ) + d z.1) at hm
      rw [z.2.2] at hm
      exact hm⟩
  have hproj (c : degreeZeroSubring G) (z : M) :
      (DirectSum.decompose 𝓜.component ((c : S) • z) n : M) =
        (c : S) • (DirectSum.decompose 𝓜.component z n : M) := by
    have hdecomp_add (u v : M) :
        DirectSum.decompose 𝓜.component (u + v) =
          DirectSum.decompose 𝓜.component u + DirectSum.decompose 𝓜.component v :=
      (DirectSum.decomposeAddEquiv 𝓜.component).map_add u v
    induction z using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp
    | add z w hz hw =>
        rw [smul_add, hdecomp_add ((c : S) • z) ((c : S) • w), hdecomp_add z w]
        change
          (DirectSum.decompose 𝓜.component ((c : S) • z) n : M) +
              (DirectSum.decompose 𝓜.component ((c : S) • w) n : M) =
            (c : S) •
              ((DirectSum.decompose 𝓜.component z n : M) +
                (DirectSum.decompose 𝓜.component w n : M))
        rw [hz, hw, smul_add]
    | @homogeneous j z =>
        have h := 𝓜.gradedSMul.smul_mem c.property z.property
        have h' : (c : S) • (z : M) ∈ 𝓜.component j := by
          change (c : S) • (z : M) ∈ 𝓜.component ((0 : ℤ) + j) at h
          simpa using h
        by_cases hj : j = n
        · subst j
          rw [DirectSum.decompose_of_mem_same 𝓜.component h',
            DirectSum.decompose_of_mem_same 𝓜.component z.property]
        · rw [DirectSum.decompose_of_mem_ne 𝓜.component h' hj,
            DirectSum.decompose_of_mem_ne 𝓜.component z.property hj]
          simp
  let hfinite := Set.finite_range cand
  refine Module.Finite.of_fg_top ⟨hfinite.toFinset, ?_⟩
  rw [hfinite.coe_toFinset]
  apply top_unique
  intro y hy
  have hyP : (y : M) ∈ P := by
    have : (y : M) ∈ N := by
      rw [hNtop]
      trivial
    exact this
  have hresult :
      (⟨(DirectSum.decompose 𝓜.component (y : M) n : M),
        (DirectSum.decompose 𝓜.component (y : M) n).property⟩ : 𝓜.component n) ∈
        Submodule.span (degreeZeroSubring G) (Set.range cand) := by
    refine Submodule.span_induction
      (p := fun z _ =>
        (⟨(DirectSum.decompose 𝓜.component z n : M),
          (DirectSum.decompose 𝓜.component z n).property⟩ : 𝓜.component n) ∈
          Submodule.span (degreeZeroSubring G) (Set.range cand)) ?_ ?_ ?_ ?_ hyP
    · rintro z ⟨⟨e, i⟩, rfl⟩
      change
        (⟨(DirectSum.decompose 𝓜.component (monomial e • x i) n : M),
          (DirectSum.decompose 𝓜.component (monomial e • x i) n).property⟩ :
            𝓜.component n) ∈ Submodule.span (degreeZeroSubring G) (Set.range cand)
      have hm := 𝓜.gradedSMul.smul_mem (hmono e) (hx i)
      change monomial e • x i ∈ 𝓜.component ((deg e : ℤ) + d i) at hm
      by_cases hdeg : (deg e : ℤ) + d i = n
      · have hp : n - d i ≥ 0 := by omega
        have hdegn : deg e = Int.toNat (n - d i) := by
          apply Int.ofNat_inj.mp
          calc
            ((deg e : ℕ) : ℤ) = n - d i := by omega
            _ = (Int.toNat (n - d i) : ℤ) := (Int.toNat_of_nonneg hp).symm
        have hebound : ∀ j : ι, e j ≤ p i := by
          intro j
          have hq : 1 ≤ qp j := by
            dsimp [qp]
            omega
          have hle : qp j * e j ≤ deg e := by
            change qp j * e j ≤ ∑ i : ι, qp i * e i
            exact Finset.single_le_sum (s := (Finset.univ : Finset ι))
              (f := fun i : ι => qp i * e i)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          have hpi : p i = deg e := by
            dsimp [p]
            simpa using hdegn.symm
          have hej : e j ≤ qp j * e j := by
            simpa using Nat.mul_le_mul_right (e j) hq
          have hejdeg : e j ≤ deg e := hej.trans hle
          rw [hpi]
          exact hejdeg
        let eb : ι → Fin (p i + 1) := fun j =>
          ⟨e j, Nat.lt_succ_of_le (hebound j)⟩
        let zD : D := ⟨i, ⟨eb, by
          dsimp [eb]
          simpa [hdegn, p] using hdeg⟩⟩
        have hcan : cand zD =
            (⟨monomial e • x i, by simpa [hdeg] using hm⟩ : 𝓜.component n) := by
          apply Subtype.ext
          dsimp [cand, zD, eb]
        have hspan : cand zD ∈
            Submodule.span (degreeZeroSubring G) (Set.range cand) :=
          Submodule.subset_span ⟨zD, rfl⟩
        have hdec :
            (DirectSum.decompose 𝓜.component (monomial e • x i) n : M) =
              monomial e • x i :=
          DirectSum.decompose_of_mem_same 𝓜.component (by simpa [hdeg] using hm)
        have htarget :
            (⟨(DirectSum.decompose 𝓜.component (monomial e • x i) n : M),
              (DirectSum.decompose 𝓜.component (monomial e • x i) n).property⟩ :
                𝓜.component n) = cand zD := by
          calc
            _ = (⟨monomial e • x i, by simpa [hdeg] using hm⟩ : 𝓜.component n) := by
              apply Subtype.ext
              exact hdec
            _ = cand zD := hcan.symm
        rw [htarget]
        exact hspan
      · have hzero :
            (DirectSum.decompose 𝓜.component (monomial e • x i) n : M) = 0 :=
          DirectSum.decompose_of_mem_ne 𝓜.component hm hdeg
        have hsub :
            (⟨(DirectSum.decompose 𝓜.component (monomial e • x i) n : M),
              (DirectSum.decompose 𝓜.component (monomial e • x i) n).property⟩ :
                𝓜.component n) = 0 := by
          apply Subtype.ext
          exact hzero
        rw [hsub]
        exact Submodule.zero_mem _
    · have hzero :
          (⟨(DirectSum.decompose 𝓜.component (0 : M) n : M),
            (DirectSum.decompose 𝓜.component (0 : M) n).property⟩ :
              𝓜.component n) = 0 := by
        apply Subtype.ext
        simp
      rw [hzero]
      exact Submodule.zero_mem _
    · intro z w _ _ hz hw
      rw [DirectSum.decompose_add, DirectSum.add_apply]
      change
        (⟨(DirectSum.decompose 𝓜.component z n : M),
          (DirectSum.decompose 𝓜.component z n).property⟩ : 𝓜.component n) +
            ⟨(DirectSum.decompose 𝓜.component w n : M),
              (DirectSum.decompose 𝓜.component w n).property⟩ ∈
          Submodule.span (degreeZeroSubring G) (Set.range cand)
      exact Submodule.add_mem _ hz hw
    · intro c z _ hz
      change
        (⟨(DirectSum.decompose 𝓜.component ((c : S) • z) n : M),
          (DirectSum.decompose 𝓜.component ((c : S) • z) n).property⟩ :
            𝓜.component n) ∈ Submodule.span (degreeZeroSubring G) (Set.range cand)
      have h := Submodule.smul_mem
        (Submodule.span (degreeZeroSubring G) (Set.range cand)) c hz
      have heq :
          (⟨(DirectSum.decompose 𝓜.component ((c : S) • z) n : M),
            (DirectSum.decompose 𝓜.component ((c : S) • z) n).property⟩ :
              𝓜.component n) =
            c •
              (⟨(DirectSum.decompose 𝓜.component z n : M),
                (DirectSum.decompose 𝓜.component z n).property⟩ :
                  𝓜.component n) := by
        apply Subtype.ext
        rw [hproj]
        exact (hsmul c _).symm
      rw [heq]
      exact h
  have hydec :
      (⟨(DirectSum.decompose 𝓜.component (y : M) n : M),
        (DirectSum.decompose 𝓜.component (y : M) n).property⟩ : 𝓜.component n) = y := by
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same 𝓜.component y.property
  rw [hydec] at hresult
  exact hresult

theorem graded_module_component_finite
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Algebra.FiniteType (degreeZeroSubring G) S] [Module.Finite S M]
    (n : ℤ) [Module (degreeZeroSubring G) (𝓜.component n)]
    (hsmul : ∀ (c : degreeZeroSubring G) (y : 𝓜.component n),
      ((c • y : 𝓜.component n) : M) = (c : S) • (y : M)) :
    Module.Finite (degreeZeroSubring G) (𝓜.component n) := by
  obtain ⟨r, q, a, ha, hagen⟩ :=
    exists_finite_homogeneous_ring_generators G
  obtain ⟨m, d, x, hx, hxspan⟩ :=
    graded_finite_homogeneous_generators G 𝓜
  exact graded_component_finite_of_homogeneous_generators
    G 𝓜 r q a ha hagen m d x hx hxspan n hsmul

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
