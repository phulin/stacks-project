import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Smooth.Quotient

/-!
# Commutative Algebra, Chapter 96: Completion

The completion in the source is Mathlib's canonical `AdicCompletion`.  Its
indexing starts at `0`, whereas the source displays positive indices; the
zeroth quotient is zero and does not change the inverse limit.  The module
completion is an `AdicCompletion`, and the ring completion and its algebra and
module structures are the instances supplied by Mathlib.
-/

namespace Formalization.Books.Algebra.Unit96

open scoped TensorProduct

universe u v w

noncomputable section

/-! ## The completion and its canonical maps -/

/-- The completion of an `R`-module with respect to `I`. -/
abbrev completion {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] : Type _ :=
  AdicCompletion I M

/-- The ring completion, viewed with Mathlib's canonical commutative-ring structure. -/
abbrev ringCompletion {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  completion I R

/-- The compatibility condition on the quotient coordinates of a completion element. -/
theorem completion_element_compatibility
    {R : Type u} [CommRing R] {I : Ideal R}
    {M : Type v} [AddCommGroup M] [Module R M]
    (x : completion I M) {m n : ℕ} (hmn : m ≤ n) :
    AdicCompletion.transitionMap I M hmn (x.val n) = x.val m := by
  exact x.property hmn

/- The source's map `M ⊗ R^ → M^` is Mathlib's `ofTensorProduct` after the
   canonical symmetry of tensor products.  The auxiliary abbreviation keeps
   the canonical Mathlib orientation available while the source-facing map
   below uses the displayed tensor order. -/
abbrev completionTensorMapCanonical {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    ringCompletion I ⊗[R] M →ₗ[ringCompletion I] completion I M :=
  AdicCompletion.ofTensorProduct I M

abbrev completionTensorMap {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    M ⊗[R] ringCompletion I →ₗ[R] completion I M :=
  (completionTensorMapCanonical I M).restrictScalars R ∘ₗ
    (TensorProduct.comm R M (ringCompletion I)).toLinearMap

/- The source-facing notation `φ^` is Mathlib's functorial completion map. -/
abbrev completionMap {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) : completion I M →ₗ[ringCompletion I] completion I N :=
  AdicCompletion.map I f

theorem completion_map_natural
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    ∀ x : M,
      completionMap I f (AdicCompletion.of I M x) = AdicCompletion.of I N (f x) := by
  intro x
  rfl

/- The statement in the source that completion is not exact is recorded as a
   functorial assertion about short exact sequences of modules. -/
def CompletionPreservesExactness {R : Type u} [CommRing R] (I : Ideal R) : Prop :=
  ∀ {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
      Function.Injective (AdicCompletion.map I f) ∧
        Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
          Function.Surjective (AdicCompletion.map I g)

theorem completion_not_exact_in_general :
    ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R),
      CompletionPreservesExactness I := by
  intro h
  let R := ULift.{u} ℤ
  let K0 := ℤ
  let M0 := ℚ
  let rhoK : R →+* K0 := ULift.ringEquiv.toRingHom
  let rhoM : R →+* M0 := (Int.castRingHom ℚ).comp rhoK
  letI : Algebra R K0 := rhoK.toAlgebra
  letI : Algebra R M0 := rhoM.toAlgebra
  let I : Ideal R := Ideal.span ({ULift.up (2 : ℤ)} : Set R)
  let K := ULift.{u_1} K0
  let M := ULift.{u_1} M0
  let rhoKU : R →+* K := (ULift.ringEquiv.symm.toRingHom).comp rhoK
  let rhoMU : R →+* M := (ULift.ringEquiv.symm.toRingHom).comp rhoM
  letI : Algebra R K := rhoKU.toAlgebra
  letI : Algebra R M := rhoMU.toAlgebra
  have hImapMU : Ideal.map rhoMU I = ⊤ := by
    change Ideal.map rhoMU (Ideal.span ({ULift.up (2 : ℤ)} : Set R)) = ⊤
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span ({(ULift.up (2 : ℚ))} : Set M) = ⊤
    rw [Ideal.span_singleton_eq_top]
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hz' := congrArg ULift.down hz
    norm_num at hz'
  have hImapKU :
      Ideal.map rhoKU I =
        Ideal.span ({ULift.up (2 : ℤ)} : Set K) := by
    change Ideal.map rhoKU (Ideal.span ({ULift.up (2 : ℤ)} : Set R)) = _
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span ({ULift.up (2 : ℤ)} : Set K) = _
    rfl
  have hpowM (n : ℕ) :
      I ^ n • (⊤ : Submodule R M) = ⊤ := by
    calc
      I ^ n • (⊤ : Submodule R M) =
          (Ideal.map (algebraMap R M) (I ^ n)).restrictScalars R :=
        Ideal.smul_top_eq_map (I ^ n)
      _ = (Ideal.map rhoMU (I ^ n)).restrictScalars R := by
        rw [RingHom.algebraMap_toAlgebra]
      _ = ((Ideal.map rhoMU I) ^ n).restrictScalars R := by
        rw [Ideal.map_pow]
      _ = ⊤ := by rw [hImapMU]; simp
  have htarget_subsingleton : Subsingleton (completion I M) := by
    constructor
    intro x y
    apply AdicCompletion.ext
    intro n
    have hquot : Subsingleton (M ⧸ (I ^ n • (⊤ : Submodule R M))) := by
      constructor
      intro a b
      induction a, b using Quotient.inductionOn₂' with | _ a b =>
        apply (Submodule.Quotient.eq _).2
        rw [hpowM n]
        exact Submodule.mem_top
    exact hquot.elim _ _
  have hI1K :
      I • (⊤ : Submodule R K) =
        (Ideal.span ({ULift.up (2 : ℤ)} : Set K)).restrictScalars R := by
    calc
      I • (⊤ : Submodule R K) =
          (Ideal.map (algebraMap R K) I).restrictScalars R :=
        Ideal.smul_top_eq_map I
      _ = (Ideal.map rhoKU I).restrictScalars R := by
        rw [RingHom.algebraMap_toAlgebra]
      _ = (Ideal.span ({ULift.up (2 : ℤ)} : Set K)).restrictScalars R := by
        rw [hImapKU]
  have hnonzero : AdicCompletion.of I K (ULift.up (1 : ℤ)) ≠ 0 := by
    intro hz
    have hcoord := congrArg (fun z => z.val 1) hz
    change Submodule.Quotient.mk (ULift.up (1 : ℤ)) =
      Submodule.Quotient.mk 0 at hcoord
    have hmem := (Submodule.Quotient.eq _).1 hcoord
    have hmem1 : ULift.up (1 : ℤ) ∈ I • (⊤ : Submodule R K) := by
      simpa using hmem
    rw [hI1K] at hmem1
    have hmem0 : ULift.up (1 : ℤ) ∈
        Ideal.span ({ULift.up (2 : ℤ)} : Set K) := hmem1
    rw [Ideal.mem_span_singleton] at hmem0
    obtain ⟨a, ha⟩ := hmem0
    have ha' := congrArg ULift.down ha
    simp at ha'
    exact (by norm_num : ¬ (2 : ℤ) ∣ 1)
      ⟨a.down, by simpa [mul_comm] using ha'⟩
  let f0 : K0 →ₗ[R] M0 :=
    { toFun := fun z => (z : ℚ)
      map_add' := by
        intro x y
        change ((x + y : ℤ) : ℚ) = (x : ℚ) + (y : ℚ)
        norm_cast
      map_smul' := by
        intro r x
        change ((rhoK r * x : ℤ) : ℚ) = (rhoK r : ℚ) * (x : ℚ)
        norm_cast }
  let P0 := M0 ⧸ LinearMap.range f0
  let g0 : M0 →ₗ[R] P0 := (LinearMap.range f0).mkQ
  have hf0 : Function.Injective f0 := by
    intro x y hxy
    change (x : ℚ) = (y : ℚ) at hxy
    exact_mod_cast hxy
  have hfg0 : Function.Exact f0 g0 := by
    exact LinearMap.exact_map_mkQ_range f0
  have hg0 : Function.Surjective g0 := Submodule.mkQ_surjective _
  let P := ULift.{u_1} P0
  letI : Module R P := ULift.module'
  let eK : K ≃ₗ[R] K0 := ULift.moduleEquiv
  let eM : M ≃ₗ[R] M0 := ULift.moduleEquiv
  let eP : P ≃ₗ[R] P0 := ULift.moduleEquiv
  let f : K →ₗ[R] M := eM.symm.toLinearMap.comp (f0.comp eK.toLinearMap)
  let g : M →ₗ[R] P := eP.symm.toLinearMap.comp (g0.comp eM.toLinearMap)
  have hf : Function.Injective f := by
    intro x y hxy
    apply eK.injective
    apply hf0
    have hxy' := congrArg eM hxy
    simpa [f] using hxy'
  have hfg : Function.Exact f g := by
    apply (LinearEquiv.conj_symm_exact_iff_exact
      (f0.comp eK.toLinearMap) (eP.symm.toLinearMap.comp g0) eM).2
    apply eP.symm.injective.comp_exact_iff_exact.2
    exact eK.surjective.comp_exact_iff_exact.2 hfg0
  have hg : Function.Surjective g := by
    intro y
    let y0 := eP y
    obtain ⟨x0, hx0⟩ := hg0 y0
    refine ⟨eM.symm x0, ?_⟩
    apply eP.injective
    simpa [g, y0] using hx0
  have H := @h R inferInstance I K M P
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      f g hf hfg hg
  have hmap : AdicCompletion.map I f
      (AdicCompletion.of I K (ULift.up (1 : ℤ))) =
      AdicCompletion.map I f 0 := Subsingleton.elim _ _
  have hz : AdicCompletion.of I K (ULift.up (1 : ℤ)) = 0 :=
    H.1 (by simpa using hmap)
  exact hnonzero hz

/-! ## Generalities -/

/- The source's first part is the canonical `map_surjective_of_mkQ_comp_surjective`
   theorem.  `LinearMap.reduceModIdeal` is the induced map on the quotients. -/
theorem completion_map_surjective_of_mod_ideal_surjective
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (hf : Function.Surjective (LinearMap.reduceModIdeal I f)) :
    Function.Surjective (AdicCompletion.map I f) := by
  apply AdicCompletion.map_surjective_of_mkQ_comp_surjective (I := I) (f := f)
  intro y
  obtain ⟨x, hx⟩ := hf y
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨m, ?_⟩
  calc
    (I • (⊤ : Submodule R N)).mkQ (f m) =
        (LinearMap.reduceModIdeal I f) (Submodule.Quotient.mk m) := rfl
    _ = (LinearMap.reduceModIdeal I f) x := congrArg _ hm
    _ = y := hx

theorem completion_map_surjective_of_surjective
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (AdicCompletion.map I f) :=
  AdicCompletion.map_surjective I hf

theorem completion_short_exact_of_flat
    {R : Type u} [CommRing R] (I : Ideal R)
    {K : Type v} [AddCommGroup K] [Module R K]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Flat R N]
    (f : K →ₗ[R] M) (g : M →ₗ[R] N)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f) (AdicCompletion.map I g) ∧
      Function.Surjective (AdicCompletion.map I g) := by
  have hfininj (J : Ideal R) :
      Function.Injective (LinearMap.reduceModIdeal J f) := by
    intro x y hxy
    induction x, y using Quotient.inductionOn₂' with | _ x y =>
      change Submodule.Quotient.mk x = Submodule.Quotient.mk y
      apply (Submodule.Quotient.eq _).2
      change Submodule.Quotient.mk (f x) = Submodule.Quotient.mk (f y) at hxy
      have hker : f x - f y ∈ g.ker := by
        change g (f x - f y) = 0
        calc
          g (f x - f y) = (g.comp f) (x - y) := by simp
          _ = 0 := by rw [hfg.linearMap_comp_eq_zero]; simp
      have hJ : f x - f y ∈ J • (⊤ : Submodule R M) :=
        (Submodule.Quotient.eq _).1 hxy
      have hp := @LinearMap.ker_inf_smul_top_eq_smul_of_flat R _ M N _ _ _ _ J g hg
      have hp' : f x - f y ∈ J • g.ker := by
        rw [← hp]
        exact ⟨hker, hJ⟩
      rw [hfg.linearMap_ker_eq, LinearMap.range_eq_map] at hp'
      have hmap :
          J • Submodule.map f (⊤ : Submodule R K) =
            Submodule.map f (J • (⊤ : Submodule R K)) := by
        rw [Submodule.map_smul'', Submodule.map_top]
      rw [hmap] at hp'
      rcases (Submodule.mem_map (f := f) (p := J • (⊤ : Submodule R K))
        (x := f x - f y)).1 hp' with ⟨z, hz, hzf⟩
      have hzy : z = x - y := hf (by simpa [map_sub] using hzf)
      simpa [← hzy] using hz
  have hpreimage (J : Ideal R) {x : M}
      (hx : x ∈ J • (⊤ : Submodule R M)) (hxker : x ∈ g.ker) :
      ∃ z : K, z ∈ J • (⊤ : Submodule R K) ∧ f z = x := by
    have hp := @LinearMap.ker_inf_smul_top_eq_smul_of_flat R _ M N _ _ _ _ J g hg
    have hp' : x ∈ J • g.ker := by
      rw [← hp]
      exact ⟨hxker, hx⟩
    rw [hfg.linearMap_ker_eq, LinearMap.range_eq_map] at hp'
    have hmap :
        J • Submodule.map f (⊤ : Submodule R K) =
          Submodule.map f (J • (⊤ : Submodule R K)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
    rw [hmap] at hp'
    rcases (Submodule.mem_map (f := f) (p := J • (⊤ : Submodule R K))
      (x := x)).1 hp' with ⟨z, hz, hzx⟩
    exact ⟨z, hz, hzx⟩
  refine ⟨?_, ?_, AdicCompletion.map_surjective I hg⟩
  · intro x y hxy
    apply AdicCompletion.ext
    intro n
    apply hfininj (I ^ n)
    simpa [AdicCompletion.map_val_apply] using congrArg (fun z => z.val n) hxy
  · refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · rw [AdicCompletion.map_comp, hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
    · intro y
      apply AdicCompletion.induction_on I M y (fun b => ?_)
      intro hz
      have hb (n : ℕ) : g (b n) ∈ (I ^ n • (⊤ : Submodule R N)) := by
        simpa using congrArg (fun x => x.val n) hz
      have h2 (n : ℕ) : ∃ d : M, ∃ y : K,
          d ∈ (I ^ n • (⊤ : Submodule R M)) ∧ f y = b n - d := by
        have h1 : g (b n) ∈ Submodule.map g (I ^ n • (⊤ : Submodule R M)) := by
          rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hg]
          exact hb n
        obtain ⟨d, hd, hgd⟩ := (Submodule.mem_map (f := g)
          (p := I ^ n • (⊤ : Submodule R M)) (x := g (b n))).1 h1
        have hzero : g (b n - d) = 0 := by
          rw [map_sub, hgd]
          abel
        obtain ⟨y, hy⟩ := (hfg (b n - d)).mp hzero
        exact ⟨d, y, hd, hy⟩
      have a0 : {x : K // f x - b 0 ∈ (I ^ 0 • (⊤ : Submodule R M))} := by
        let d := (h2 0).choose
        let y := (h2 0).choose_spec.choose
        refine ⟨y, ?_⟩
        have hy := (h2 0).choose_spec.choose_spec.2
        have hd := (h2 0).choose_spec.choose_spec.1
        simpa [hy] using (Submodule.neg_mem _ hd)
      have aS (n : ℕ)
          (an : {x : K // f x - b n ∈ (I ^ n • (⊤ : Submodule R M))}) :
          {x : K // f x - b (n + 1) ∈
            (I ^ (n + 1) • (⊤ : Submodule R M))} := by
        let d := (h2 (n + 1)).choose
        let y := (h2 (n + 1)).choose_spec.choose
        have hy := (h2 (n + 1)).choose_spec.choose_spec.2
        have hd := (h2 (n + 1)).choose_spec.choose_spec.1
        have hdiff : f (y - an.1) ∈ (I ^ n • (⊤ : Submodule R M)) := by
          have hbn : b (n + 1) - b n ∈ (I ^ n • (⊤ : Submodule R M)) :=
            SModEq.sub_mem.mp (b.property (Nat.le_succ n)).symm
          have hdn : d ∈ (I ^ n • (⊤ : Submodule R M)) :=
            (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))) hd
          have han := an.2
          rw [map_sub, hy]
          convert_to (b (n + 1) - b n) - d - (f an.1 - b n) ∈
            (I ^ n • (⊤ : Submodule R M))
          · abel
          · exact Submodule.sub_mem _ (Submodule.sub_mem _ hbn hdn) han
        have hdiffker : f (y - an.1) ∈ g.ker := by
          change g (f (y - an.1)) = 0
          rw [← LinearMap.comp_apply, hfg.linearMap_comp_eq_zero]
          simp
        let hp := hpreimage (I ^ n) hdiff hdiffker
        let c := hp.choose
        have hc := hp.choose_spec.1
        have hfc := hp.choose_spec.2
        refine ⟨an.1 + c, ?_⟩
        have hcalc : f (an.1 + c) - b (n + 1) = -d := by
          rw [map_add, hfc, map_sub, hy]
          abel
        rw [hcalc]
        exact Submodule.neg_mem _ hd
      have a (n : ℕ) :
          {x : K // f x - b n ∈ (I ^ n • (⊤ : Submodule R M))} := by
        induction n with
        | zero => exact a0
        | succ n ih => exact aS n ih
      refine ⟨AdicCompletion.mk I K (AdicCompletion.AdicCauchySequence.mk I K
        (fun n => (a n : K)) ?_), ?_⟩
      · intro n
        apply SModEq.sub_mem.mpr
        have han := (a n).property
        have hanext := (a (n + 1)).property
        have hbn : b (n + 1) - b n ∈ (I ^ n • (⊤ : Submodule R M)) :=
          SModEq.sub_mem.mp (b.property (Nat.le_succ n)).symm
        have hdiff : f ((a (n + 1) : K) - (a n : K)) ∈
            (I ^ n • (⊤ : Submodule R M)) := by
          rw [map_sub]
          convert_to (f (a (n + 1) : K) - b (n + 1)) -
              (f (a n : K) - b n) + (b (n + 1) - b n) ∈
              (I ^ n • (⊤ : Submodule R M))
          · abel
          · have hanext' : f (a (n + 1) : K) - b (n + 1) ∈
                (I ^ n • (⊤ : Submodule R M)) :=
              Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n))
                hanext
            exact Submodule.add_mem _ (Submodule.sub_mem _ hanext' han) hbn
        have hdiffker : f ((a (n + 1) : K) - (a n : K)) ∈ g.ker := by
          change g (f ((a (n + 1) : K) - (a n : K))) = 0
          rw [← LinearMap.comp_apply, hfg.linearMap_comp_eq_zero]
          simp
        obtain ⟨c, hc, hfc⟩ := hpreimage (I ^ n) hdiff hdiffker
        have heq : c = (a (n + 1) : K) - (a n : K) :=
          hf (by simpa using hfc)
        simpa [heq] using (Submodule.neg_mem _ hc)
      · ext n
        change Submodule.Quotient.mk (f (a n)) =
          Submodule.Quotient.mk (b n)
        exact (Submodule.Quotient.eq _).2 (a n).property

theorem completion_tensor_map_surjective_of_finite
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (completionTensorMap I M) := by
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  obtain ⟨x, rfl⟩ := (TensorProduct.comm R M (ringCompletion I)).surjective z
  exact ⟨x, rfl⟩

/-! ## Completeness -/

/-- The source's definition of adic completeness in Mathlib's canonical form. -/
theorem isAdicComplete_iff_completion_map_bijective
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I M ↔ Function.Bijective (AdicCompletion.of I M) := by
  exact AdicCompletion.of_bijective_iff.symm

/- The source records that a completion need not be complete when the ideal is
   not finitely generated. -/
theorem completion_not_complete_in_general :
    ¬ ∀ (R : Type u) [CommRing R] (I : Ideal R)
      (M : Type v) [AddCommGroup M] [Module R M],
      IsAdicComplete I (completion I M) := by
  sorry

/- The footnote in the source is the Hausdorff/separated part of the canonical
   `IsAdicComplete` class. -/
theorem isAdicComplete_separated
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsAdicComplete I M) :
    (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⊥ := by
  exact IsHausdorff.iInf_pow_smul hM.toIsHausdorff

/-! ## The double-completion calculation -/

theorem completion_isAdicComplete_of_fg
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (hI : I.FG) :
    IsAdicComplete I (completion I M) := by
  exact AdicCompletion.isAdicComplete hI

theorem completion_pow_smul_eq_kernel_eval
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (hI : I.FG) (n : ℕ) :
    I ^ n • (⊤ : Submodule R (completion I M)) =
      (AdicCompletion.eval I M n).ker := by
  exact AdicCompletion.pow_smul_top_eq_ker_eval hI

/- The completion of `I^n M` is represented by the canonical inclusion of the
   completion of `I^n • M`; its range is the kernel above. -/
theorem completion_of_power_range_eq_kernel_eval
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    (AdicCompletion.ofPowSMul I M n).range.restrictScalars R =
      (AdicCompletion.eval I M n).ker := by
  exact AdicCompletion.restrictScalars_range_ofPowSMul_eq_ker_eval
    (I := I) (M := M) (n := n)

/-- The extension of `I^n` to the ring completion. -/
def completionPowerIdeal
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    Ideal (ringCompletion I) :=
  (I ^ n).map (algebraMap R (ringCompletion I))

/- This packages the source's `R^/I^nR^ = R/I^n` assertion using the
   canonical quotient map `evalₐ`. -/
theorem completion_quotient_power_equiv
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) (n : ℕ) :
    ∃ e : (ringCompletion I ⧸ completionPowerIdeal I n) ≃ₐ[R] (R ⧸ I ^ n),
      ∀ x : ringCompletion I,
        e (Ideal.Quotient.mk (completionPowerIdeal I n) x) =
          AdicCompletion.evalₐ I n x := by
  sorry

/-! ## Completion modulo a power-torsion quotient -/

/- `I^c • Q = 0` is the module form of saying that `Q` is annihilated by a
   power of `I`. -/
theorem isAdicComplete_of_power_annihilated
    {R : Type u} [CommRing R] (I : Ideal R)
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (hQ : ∃ c : ℕ, I ^ c • (⊤ : Submodule R Q) = ⊥) :
    IsAdicComplete I Q := by
  sorry

noncomputable def completionToPowerAnnihilated
    {R : Type u} [CommRing R] (I : Ideal R)
    (Q : Type v) [AddCommGroup Q] [Module R Q]
    (hQ : ∃ c : ℕ, I ^ c • (⊤ : Submodule R Q) = ⊥) :
    completion I Q ≃ₗ[R] Q := by
  letI : IsAdicComplete I Q := isAdicComplete_of_power_annihilated I hQ
  exact (AdicCompletion.ofLinearEquiv I Q).symm

noncomputable def completionMapToPowerAnnihilated
    {R : Type u} [CommRing R] (I : Ideal R)
    {N Q : Type v} [AddCommGroup N] [AddCommGroup Q]
    [Module R N] [Module R Q]
    (g : N →ₗ[R] Q)
    (hQ : ∃ c : ℕ, I ^ c • (⊤ : Submodule R Q) = ⊥) :
    completion I N →ₗ[R] Q :=
  (completionToPowerAnnihilated I Q hQ).toLinearMap ∘ₗ
    (AdicCompletion.map I g).restrictScalars R

theorem completion_exact_of_power_annihilated_quotient
    {R : Type u} [CommRing R] (I : Ideal R)
    {K : Type v} [AddCommGroup K] [Module R K]
    {N Q : Type w} [AddCommGroup N] [AddCommGroup Q]
    [Module R N] [Module R Q]
    (f : K →ₗ[R] N) (g : N →ₗ[R] Q)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g)
    (hQ : ∃ c : ℕ, I ^ c • (⊤ : Submodule R Q) = ⊥) :
    Function.Injective (AdicCompletion.map I f) ∧
      Function.Exact (AdicCompletion.map I f)
        (completionMapToPowerAnnihilated I g hQ) ∧
        Function.Surjective (completionMapToPowerAnnihilated I g hQ) := by
  sorry

/-! ## The kernel criterion for the double completion -/

/-- The kernel of the `n`th coordinate map of a module completion. -/
abbrev completionKernel
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule R (completion I M) :=
  (AdicCompletion.eval I M n).ker

theorem completion_isAdicComplete_iff_kernel_eq_power
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsAdicComplete I (completion I M) ↔
      ∀ n : ℕ, 1 ≤ n →
        completionKernel I M n = I ^ n • (⊤ : Submodule R (completion I M)) := by
  sorry

/-! ## Units and the Jacobson radical -/

theorem completion_radical
    {R : Type u} [CommRing R] (I : Ideal R) :
    (∀ x : ringCompletion I,
        IsUnit (AdicCompletion.evalOneₐ I x) → IsUnit x) ∧
      (∀ r : R, r ∈ I →
        IsUnit (1 + algebraMap R (ringCompletion I) r)) ∧
      (∀ x : ringCompletion I, x ∈ I.map (algebraMap R (ringCompletion I)) →
        IsUnit (1 + x)) ∧
      I.map (algebraMap R (ringCompletion I)) ≤ Ring.jacobson (ringCompletion I) ∧
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom ≤
        Ring.jacobson (ringCompletion I) := by
  sorry

/-! ## Finitely generated ideals and completeness -/

theorem surjective_to_completion_of_finite_generators
    (A : Type u) [CommRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (r : ℕ) (f : Fin r → A)
    (hI : I = Ideal.span (Set.range f))
    (hf : ∀ i : Fin r,
      Function.Surjective (AdicCompletion.of (Ideal.span ({f i} : Set A)) M)) :
    Function.Surjective (AdicCompletion.of I M) := by
  sorry

theorem isAdicComplete_of_le_of_fg
    {R : Type u} [CommRing R] (I J : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hIJ : I ≤ J) (hJ : IsAdicComplete J M) (hI : I.FG) :
    IsAdicComplete I M := by
  sorry

theorem completion_equiv_of_power_le
    {R : Type u} [CommRing R] (I J : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    Nonempty (completion I M ≃ₗ[R] completion J M) := by
  sorry

theorem isAdicComplete_iff_of_power_le
    {R : Type u} [CommRing R] (I J : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d)
    (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  sorry

/-! ## Complete quotients -/

theorem quotient_isAdicComplete_iff
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hM : IsAdicComplete I M) (K : Submodule R M) :
    K = ⨅ n : ℕ, K ⊔ I ^ n • (⊤ : Submodule R M) ↔
      IsAdicComplete I (M ⧸ K) := by
  sorry

theorem finite_module_isAdicComplete_of_complete_ring
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hR : IsAdicComplete I R)
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⊥) :
    IsAdicComplete I M := by
  sorry

theorem finite_of_complete_ring_of_finite_residue
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    (hR : IsAdicComplete I R)
    (hM : (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)) = ⊥)
    [Module.Finite (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))] :
    Module.Finite R M := by
  sorry

end

end Formalization.Books.Algebra.Unit96
