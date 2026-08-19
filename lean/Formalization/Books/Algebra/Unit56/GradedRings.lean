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

theorem tensorProduct_decomposition_exists
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (𝓝 : GradedModuleData G N) :
    Nonempty (DirectSum.Decomposition (tensorProductComponent G 𝓜 𝓝)) := by
  sorry
/-
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
  let : DirectSum.Decomposition CM :=
    DirectSum.Decomposition.ofAddHom CM decompM hleftM hrightM
  let : DirectSum.Decomposition CN :=
    DirectSum.Decomposition.ofAddHom CN decompN hleftN hrightN
  let CT : ℤ → Submodule (degreeZeroSubring G) (TensorProduct S M N) :=
    fun d => Submodule.span (degreeZeroSubring G)
      (tensorProductHomogeneousTensors G 𝓜 𝓝 d)
  let V := (⨁ d, CT d)
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
      TensorProduct (degreeZeroSubring G) (CM p.1) (CN p.2)) →ₗ[degreeZeroSubring G] V :=
    DirectSum.toModule (degreeZeroSubring G) _ _ fun p =>
      (DirectSum.lof (degreeZeroSubring G) ℤ (fun d => CT d) (p.1 + p.2)).comp
        (pairMapCT p.1 p.2)
  let F₀ : TensorProduct (degreeZeroSubring G) M N →ₗ[degreeZeroSubring G] V :=
    g.comp sourceEquiv.toLinearMap
  have hF₀_hom (i j : ℤ) (m : CM i) (n : CN j) :
      F₀ ((m : M) ⊗ₜ[degreeZeroSubring G] (n : N)) =
        DirectSum.of (fun d => CT d) (i + j)
          ⟨(m : M) ⊗ₜ[S] (n : N), Submodule.subset_span
            ⟨i, j, rfl, m, m.property, n, n.property, rfl⟩⟩ := by
    simp [F₀, sourceEquiv, directSumEquiv, g, pairMapCT, pairMap, q,
      TensorProduct.directSum_lof_tmul_lof, LinearMap.codRestrict]
    rw [DirectSum.lof_eq_of]
  let f : M →+ N →+ V :=
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
  let F : TensorProduct S M N →+ V := TensorProduct.liftAddHom f hbal
  let coe : V →+ TensorProduct S M N := DirectSum.coeAddMonoidHom CT
  have hf (x : M) (y : N) :
      f x y = F₀ (x ⊗ₜ[degreeZeroSubring G] y) := rfl
  have hF_tmul (x : M) (y : N) : F (x ⊗ₜ[S] y) = f x y :=
    TensorProduct.liftAddHom_tmul f hbal x y
  have hF₀_hom_recompose (x : M) (z : N) :
      coe (F₀ (x ⊗ₜ[degreeZeroSubring G] z)) = q (x ⊗ₜ[degreeZeroSubring G] z) := by
    /- Prior attempt: the direct-sum recomposition induction left dependent
       subtype proofs after rewriting the homogeneous cases. -/
    induction x using DirectSum.Decomposition.inductionOn
        (ℳ := 𝓜.component) with
    | zero => simp [F₀, coe, q]
    | add x y hx hy =>
        simpa [F₀, coe, q, TensorProduct.add_tmul] using
          congrArg₂ (· + ·) hx hy
    | @homogeneous i x =>
        induction z using DirectSum.Decomposition.inductionOn
            (ℳ := 𝓝.component) with
        | zero => simp [F₀, coe, q]
        | add z z' hz hz' =>
            simpa [F₀, coe, q, TensorProduct.tmul_add] using
              congrArg₂ (· + ·) hz hz'
        | @homogeneous j z =>
            rw [hF₀_hom i j ⟨(x : M), by simpa [CM] using x.property⟩
              ⟨(z : N), by simpa [CN] using z.property⟩]
            change DirectSum.coeAddMonoidHom CT
                ((of (fun d => CT d) (i + j))
                  ⟨(x : M) ⊗ₜ[S] (z : N), _⟩) = _
            rw [DirectSum.coeAddMonoidHom_of]
            simp [q]
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
  have hF_smul (c : degreeZeroSubring G) (x : TensorProduct S M N) :
      F ((c : S) • x) = c • F x := by
    /- Prior attempt: scalar compatibility required the same dependent
       transport as the preceding recomposition argument. -/
    sorry
  have hright : F.comp coe = AddMonoidHom.id _ := by
    /- Prior attempt: the span induction did not retain the component
       family through the dependent direct-sum coercion. -/
    refine directSum_span_right_inverse
      (A := degreeZeroSubring G) (M := TensorProduct S M N) (I := ℤ)
      CT (fun d => tensorProductHomogeneousTensors G 𝓜 𝓝 d)
      (fun d => by rfl) F hgen hF_smul
  /- Prior attempt: the constructed direct sum uses submodule subtypes,
     while the theorem's decomposition is indexed by add-subgroup subtypes. -/
  exact ⟨by sorry⟩ -/

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
