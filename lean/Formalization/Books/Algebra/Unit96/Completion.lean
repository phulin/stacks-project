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
  intro hall
  let B := MvPolynomial ℕ ℤ
  let R := MvPolynomial ℕ (ULift.{u} ℤ)
  let coeffDown : ULift.{u} ℤ →+* ℤ := ULift.ringEquiv.toRingHom
  let φ : R →+* B := MvPolynomial.map coeffDown
  let I : Ideal R := MvPolynomial.idealOfVars ℕ (ULift.{u} ℤ)
  let M := ULift.{v} B
  let _ : Module R M := Module.compHom M φ
  let A := completion I M
  have hA : IsAdicComplete I A := hall R I M
  let pB (n : ℕ) : B :=
    Finset.sum (Finset.range n) (fun i => (MvPolynomial.X i : B) ^ (i + 1))
  let pM (n : ℕ) : M := ULift.up (pB n)
  let c : AdicCompletion.AdicCauchySequence I M :=
    AdicCompletion.AdicCauchySequence.mk I M pM (by
      intro n
      apply (SModEq.sub_mem).2
      have hmem :
          (MvPolynomial.X n : R) ^ (n + 1) ∈ I ^ n := by
        rw [show I = MvPolynomial.idealOfVars ℕ (ULift.{u} ℤ) by rfl]
        rw [MvPolynomial.X_pow_eq_monomial]
        apply (MvPolynomial.monomial_mem_pow_idealOfVars_iff n
          (Finsupp.single n (n + 1)) (by simp)).2
        simp
      have hneg : -((MvPolynomial.X n : R) ^ (n + 1)) ∈ I ^ n :=
        (I ^ n).neg_mem hmem
      have hnegM : -(⟨(MvPolynomial.X n : B) ^ (n + 1)⟩ : M) ∈
          I ^ n • (⊤ : Submodule R M) := by
        have hs := Submodule.smul_mem_smul hneg
          (show (⟨(1 : B)⟩ : M) ∈ (⊤ : Submodule R M) by simp)
        have heq :
            (-(MvPolynomial.X n : R) ^ (n + 1)) • (⟨(1 : B)⟩ : M) =
              -(⟨(MvPolynomial.X n : B) ^ (n + 1)⟩ : M) := by
          apply ULift.ext
          change φ (-(MvPolynomial.X n : R) ^ (n + 1)) * (1 : B) =
            -((MvPolynomial.X n : B) ^ (n + 1))
          rw [map_neg, map_pow]
          simp only [mul_one]
          dsimp [φ]
          rw [MvPolynomial.map_X]
        rw [← heq]
        exact hs
      have hdiff : pM n - pM (n + 1) =
          -(⟨(MvPolynomial.X n : B) ^ (n + 1)⟩ : M) := by
        apply ULift.ext
        change pB n - pB (n + 1) = -(MvPolynomial.X n : B) ^ (n + 1)
        rw [show pB (n + 1) = pB n + (MvPolynomial.X n : B) ^ (n + 1) by
          simp [pB, Finset.sum_range_succ]]
        abel
      rw [hdiff]
      exact hnegM)
  have hmap_smul (n : ℕ) :
      Submodule.map (AdicCompletion.of I M) (I ^ n • (⊤ : Submodule R M)) ≤
        I ^ n • (⊤ : Submodule R A) := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact Submodule.smul_induction_on
      (p := fun y : M => AdicCompletion.of I M y ∈
        I ^ n • (⊤ : Submodule R A)) hy
      (fun r hr y hy => by
        simp only [LinearMap.map_smul]
        exact Submodule.smul_mem_smul hr (show y ∈ (⊤ : Submodule R M) by simp))
      (fun x y hx hy => by
        rw [map_add]
        exact Submodule.add_mem _ hx hy)
  let a : ℕ → A := fun n => AdicCompletion.of I M (pM n)
  have ha : ∀ {m n : ℕ}, m ≤ n →
      a m ≡ a n [SMOD (I ^ m • (⊤ : Submodule R A))] := by
    intro m n hmn
    apply (SModEq.sub_mem).2
    change (AdicCompletion.of I M (pM m) - AdicCompletion.of I M (pM n)) ∈
      I ^ m • (⊤ : Submodule R A)
    apply hmap_smul m
    refine ⟨pM m - pM n, (SModEq.sub_mem).mp (c.property hmn), rfl⟩
  obtain ⟨y, hy⟩ := hA.toIsPrecomplete.prec ha
  let S := MvPolynomial (Fin 1) ℤ
  let N := ULift.{v} S
  let evalm (n : ℕ) : B →+* S :=
    MvPolynomial.eval₂Hom (MvPolynomial.C)
      (fun i => if i = n then (MvPolynomial.X 0 : S) else 0)
  let ρ (n : ℕ) : R →+* S := (evalm n).comp φ
  let bad (n : ℕ) (x : A) : Prop :=
    let _ : Module R N := Module.compHom N (ρ n)
    let f : M →ₗ[R] N :=
      { toFun := fun z => ⟨evalm n z.down⟩
        map_add' := by
          intro z z'
          apply ULift.ext
          change evalm n (z.down + z'.down) =
            evalm n z.down + evalm n z'.down
          rw [map_add]
        map_smul' := by
          intro r z
          apply ULift.ext
          change evalm n (φ r * z.down) = ρ n r * evalm n z.down
          rw [map_mul]
          rfl }
    AdicCompletion.map I f x = 0
  have hconst (r : R) (hr : r ∈ I) : r.constantCoeff = 0 := by
    change r ∈ MvPolynomial.idealOfVars ℕ (ULift.{u} ℤ) at hr
    rw [MvPolynomial.idealOfVars_eq_restrictSupportIdeal] at hr
    change r ∈ MvPolynomial.restrictSupport (ULift.{u} ℤ)
      (Finsupp.degree ⁻¹' Set.Ici 1) at hr
    have hzero : (0 : ℕ →₀ ℕ) ∉ r.support := by
      intro hz
      have hdeg : Finsupp.degree (0 : ℕ →₀ ℕ) ∈ Set.Ici 1 := hr hz
      simp at hdeg
    change MvPolynomial.coeff 0 r = 0
    apply not_ne_iff.mp
    intro hne
    apply hzero
    exact MvPolynomial.mem_support_iff.mpr hne
  have hgen (r : R) (hr : r ∈ I) :
      ∃ s : Finset ℕ, ∀ n ∉ s, ρ n r = 0 := by
    refine ⟨r.vars, ?_⟩
    intro n hn
    have hvars : ∀ i ∈ r.vars,
        (if i = n then (MvPolynomial.X 0 : S) else 0) = 0 := by
      intro i hi
      by_cases hin : i = n
      · exact (hn (hin ▸ hi)).elim
      · simp [hin]
    rw [show ρ n r =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp coeffDown)
        (fun i => if i = n then (MvPolynomial.X 0 : S) else 0) r by
      dsimp [ρ, evalm, φ]
      rw [MvPolynomial.eval₂Hom_map_hom]
      rfl]
    rw [MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars _ hvars]
    simp [hconst r hr]
  have hzero (n : ℕ) (r : R) (hr : ρ n r = 0) (z : A) :
      bad n (r • z) := by
    let _ : Module R N := Module.compHom N (ρ n)
    let f : M →ₗ[R] N :=
      { toFun := fun z => ⟨evalm n z.down⟩
        map_add' := by
          intro z z'
          apply ULift.ext
          change evalm n (z.down + z'.down) =
            evalm n z.down + evalm n z'.down
          rw [map_add]
        map_smul' := by
          intro r z
          apply ULift.ext
          change evalm n (φ r * z.down) = ρ n r * evalm n z.down
          rw [map_mul]
          rfl }
    change AdicCompletion.map I f (r • z) = 0
    apply AdicCompletion.ext
    intro k
    simp only [AdicCompletion.map_val_apply]
    rw [show (r • z).val k = r • z.val k by rfl]
    induction z.val k using Quotient.inductionOn' with
    | _ q =>
        change (f.reduceModIdeal (I ^ k))
          (r • (Submodule.Quotient.mk q)) = 0
        rw [← Submodule.Quotient.mk_smul, LinearMap.reduceModIdeal_apply]
        rw [map_smul]
        rw [Submodule.Quotient.mk_eq_zero]
        change (⟨ρ n r * evalm n q.down⟩ : N) ∈ I ^ k • (⊤ : Submodule R N)
        rw [hr, zero_mul]
        exact (I ^ k • (⊤ : Submodule R N)).zero_mem
  have hadd (n : ℕ) (x x' : A) (hx : bad n x) (hx' : bad n x') :
      bad n (x + x') := by
    let _ : Module R N := Module.compHom N (ρ n)
    let f : M →ₗ[R] N :=
      { toFun := fun z => ⟨evalm n z.down⟩
        map_add' := by
          intro z z'
          apply ULift.ext
          change evalm n (z.down + z'.down) =
            evalm n z.down + evalm n z'.down
          rw [map_add]
        map_smul' := by
          intro r z
          apply ULift.ext
          change evalm n (φ r * z.down) = ρ n r * evalm n z.down
          rw [map_mul]
          rfl }
    change AdicCompletion.map I f x = 0 at hx
    change AdicCompletion.map I f x' = 0 at hx'
    change AdicCompletion.map I f (x + x') = 0
    simp [map_add, hx, hx']
  have hmap (x : A) (hx : x ∈ I • (⊤ : Submodule R A)) :
      ∃ s : Finset ℕ, ∀ n ∉ s, bad n x := by
    refine Submodule.smul_induction_on
      (p := fun x : A => ∃ s : Finset ℕ, ∀ n ∉ s, bad n x) hx
      (fun r hr z hz => by
        obtain ⟨s, hs⟩ := hgen r hr
        refine ⟨r.vars ∪ s, ?_⟩
        intro n hn
        apply hzero n r (hs n (fun h => hn (Finset.mem_union_right _ h))) z)
      (fun x x' hx hx' => by
        obtain ⟨s, hs⟩ := hx
        obtain ⟨s', hs'⟩ := hx'
        refine ⟨s ∪ s', ?_⟩
        intro n hn
        apply hadd n x x'
        · exact hs n (fun h => hn (Finset.mem_union_left _ h))
        · exact hs' n (fun h => hn (Finset.mem_union_right _ h)))
  let J : Ideal S := MvPolynomial.idealOfVars (Fin 1) ℤ
  have hbase (n : ℕ) : Ideal.map (ρ n) I ≤ J := by
    rw [show I = MvPolynomial.idealOfVars ℕ (ULift.{u} ℤ) by rfl,
      MvPolynomial.idealOfVars]
    refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    by_cases hin : i = n
    · subst i
      change ρ n (MvPolynomial.X n : R) ∈ J
      dsimp [ρ, evalm, φ]
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      simp only [if_pos]
      change (MvPolynomial.X 0 : S) ∈
        Ideal.span (Set.range (MvPolynomial.X : Fin 1 → S))
      exact Ideal.subset_span ⟨0, rfl⟩
    · change ρ n (MvPolynomial.X i : R) ∈ J
      dsimp [ρ, evalm, φ]
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      simp only [if_neg hin]
      exact J.zero_mem
  have hpowI (n k : ℕ) : Ideal.map (ρ n) (I ^ k) ≤ J ^ k := by
    rw [Ideal.map_pow]
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
        rw [pow_succ, pow_succ]
        exact Ideal.mul_mono ih (hbase n)
  have hdown (n k : ℕ) :
      letI : Module R N := Module.compHom N (ρ n)
      ∀ (q : N), q ∈ I ^ k • (⊤ : Submodule R N) → q.down ∈ J ^ k := by
    let _ : Module R N := Module.compHom N (ρ n)
    intro q hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro r hr z hz
      have hr' : ρ n r ∈ J ^ k :=
        hpowI n k (Ideal.mem_map_of_mem (ρ n) hr)
      change ρ n r * z.down ∈ J ^ k
      exact (J ^ k).mul_mem_right z.down hr'
    · intro x x' hx hx'
      change x.down + x'.down ∈ J ^ k
      exact (J ^ k).add_mem hx hx'
  have hp (n : ℕ) :
      evalm n (pB (n + 2)) = (MvPolynomial.X 0 : S) ^ (n + 1) := by
    dsimp [evalm]
    simp only [pB, map_sum, map_pow]
    rw [Finset.sum_eq_single n]
    · rw [MvPolynomial.eval₂Hom_X']
      simp only [if_pos]
    · intro i hi hne
      rw [MvPolynomial.eval₂Hom_X']
      simp [hne]
    · simp
  have hnot (n : ℕ) :
      (MvPolynomial.X 0 : S) ^ (n + 1) ∉ J ^ (n + 2) := by
    change (MvPolynomial.X 0 : S) ^ (n + 1) ∉
      MvPolynomial.idealOfVars (Fin 1) ℤ ^ (n + 2)
    rw [MvPolynomial.X_pow_eq_monomial]
    intro hh
    have hdeg :=
      (MvPolynomial.monomial_mem_pow_idealOfVars_iff (n + 2)
        (Finsupp.single (0 : Fin 1) (n + 1)) (by simp)).1 hh
    simp at hdeg
  have hx0 : (MvPolynomial.X 0 : R) ∈ I := by
    change (MvPolynomial.X 0 : R) ∈
      Ideal.span (Set.range (MvPolynomial.X : ℕ → R))
    exact Ideal.subset_span ⟨0, rfl⟩
  have hx0M : pM 1 ∈ I • (⊤ : Submodule R M) := by
    change (⟨pB 1⟩ : M) ∈ I • (⊤ : Submodule R M)
    rw [show pB 1 = (MvPolynomial.X 0 : B) by
      simp [pB, Finset.sum_range_succ]]
    have hs := Submodule.smul_mem_smul hx0
      (show (⟨(1 : B)⟩ : M) ∈ (⊤ : Submodule R M) by simp)
    have heq : (MvPolynomial.X 0 : R) • (⟨(1 : B)⟩ : M) =
        (⟨(MvPolynomial.X 0 : B)⟩ : M) := by
      apply ULift.ext
      change φ (MvPolynomial.X 0 : R) * (1 : B) = MvPolynomial.X 0
      dsimp [φ]
      rw [MvPolynomial.map_X]
      simp
    rw [← heq]
    exact hs
  have ha1 : a 1 ∈ I • (⊤ : Submodule R A) := by
    change AdicCompletion.of I M (pM 1) ∈ I • (⊤ : Submodule R A)
    have hx0M' : pM 1 ∈ I ^ 1 • (⊤ : Submodule R M) := by
      simpa only [pow_one] using hx0M
    simpa only [pow_one] using (hmap_smul 1 ⟨pM 1, hx0M', rfl⟩)
  have hyI : y ∈ I • (⊤ : Submodule R A) := by
    have hdiff : a 1 - y ∈ I • (⊤ : Submodule R A) := by
      simpa only [pow_one] using (SModEq.sub_mem.mp (hy 1))
    have hmem := Submodule.sub_mem (I • (⊤ : Submodule R A)) ha1 hdiff
    simpa only [sub_sub_cancel] using hmem
  obtain ⟨s, hs⟩ := hmap y hyI
  have hnotbad (n : ℕ) : ¬ bad n y := by
    let _ : Module R N := Module.compHom N (ρ n)
    let f : M →ₗ[R] N :=
      { toFun := fun z => ⟨evalm n z.down⟩
        map_add' := by
          intro z z'
          apply ULift.ext
          change evalm n (z.down + z'.down) =
            evalm n z.down + evalm n z'.down
          rw [map_add]
        map_smul' := by
          intro r z
          apply ULift.ext
          change evalm n (φ r * z.down) = ρ n r * evalm n z.down
          rw [map_mul]
          rfl }
    intro hby
    have hdiff : a (n + 2) - y ∈ I ^ (n + 2) • (⊤ : Submodule R A) :=
      (SModEq.sub_mem.mp (hy (n + 2)))
    have heval :=
      (AdicCompletion.pow_smul_top_le_ker_eval I (n + 2)) hdiff
    have hcoord : y.val (n + 2) = (a (n + 2)).val (n + 2) := by
      change (a (n + 2)).val (n + 2) - y.val (n + 2) = 0 at heval
      exact (sub_eq_zero.mp heval).symm
    change AdicCompletion.map I f y = 0 at hby
    have hz : (AdicCompletion.map I f y).val (n + 2) = 0 := by
      simpa using congrArg (fun q => q.val (n + 2)) hby
    rw [AdicCompletion.map_val_apply, hcoord] at hz
    change (f.reduceModIdeal (I ^ (n + 2)))
        (Submodule.Quotient.mk (p := I ^ (n + 2) • (⊤ : Submodule R M))
          (pM (n + 2))) = 0 at hz
    rw [LinearMap.reduceModIdeal_apply] at hz
    have hmem : f (pM (n + 2)) ∈ I ^ (n + 2) • (⊤ : Submodule R N) := by
      rw [Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    have hfp : f (pM (n + 2)) =
        (⟨(MvPolynomial.X 0 : S) ^ (n + 1)⟩ : N) := by
      apply ULift.ext
      change evalm n (pB (n + 2)) = (MvPolynomial.X 0 : S) ^ (n + 1)
      exact hp n
    rw [hfp] at hmem
    exact hnot n (hdown n (n + 2) _ hmem)
  by_cases hs0 : s.Nonempty
  · let n := s.max' hs0 + 1
    have hn : n ∉ s := by
      intro hn
      have hle := Finset.le_max' s n hn
      dsimp [n] at hle
      omega
    exact (hnotbad n) (hs n hn)
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs0
    subst s
    exact (hnotbad 0) (hs 0 (by simp))

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
  classical
  have hsurj : Function.Surjective (AdicCompletion.evalₐ I n) :=
    AdicCompletion.surjective_evalₐ I n
  have hp :
      I ^ n • (⊤ : Submodule R (completion I R)) =
        (AdicCompletion.eval I R n).ker :=
    AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := R) (n := n) hI
  have hker :
      RingHom.ker (AdicCompletion.evalₐ I n) =
        completionPowerIdeal I n := by
    ext x
    change AdicCompletion.evalₐ I n x = 0 ↔
      x ∈ (I ^ n).map (algebraMap R (ringCompletion I))
    constructor
    · intro hx
      have hx' := congrArg (Ideal.Quotient.factor
        (show I ^ n ≤ I ^ n • (⊤ : Ideal R) by simp)) hx
      rw [AdicCompletion.factor_evalₐ_eq_eval, map_zero] at hx'
      have hmem : x ∈ I ^ n • (⊤ : Submodule R (completion I R)) := by
        rw [hp]
        exact LinearMap.mem_ker.mpr hx'
      change x ∈ ((I ^ n).map (algebraMap R (ringCompletion I))).restrictScalars R
      rw [← Ideal.smul_top_eq_map]
      exact hmem
    · intro hx
      have hmem : x ∈ I ^ n • (⊤ : Submodule R (completion I R)) := by
        change x ∈ ((I ^ n).map (algebraMap R (ringCompletion I))).restrictScalars R at hx
        rw [← Ideal.smul_top_eq_map] at hx
        exact hx
      have hker_mem : x ∈ (AdicCompletion.eval I R n).ker := by
        rw [← hp]
        exact hmem
      have heval : AdicCompletion.eval I R n x = 0 := LinearMap.mem_ker.mp hker_mem
      have hfactor :
          Ideal.Quotient.factor (show I ^ n • (⊤ : Ideal R) ≤ I ^ n by simp)
              (AdicCompletion.eval I R n x) = AdicCompletion.evalₐ I n x :=
        AdicCompletion.factor_eval_eq_evalₐ (I := I) (R := R) x (by simp)
      calc
        AdicCompletion.evalₐ I n x =
            Ideal.Quotient.factor (show I ^ n • (⊤ : Ideal R) ≤ I ^ n by simp)
              (AdicCompletion.eval I R n x) := hfactor.symm
        _ = 0 := by rw [heval, map_zero]
  let e₀ := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let e := (Ideal.quotientEquivAlgOfEq R hker.symm).trans e₀
  refine ⟨e, ?_⟩
  intro x
  dsimp [e, e₀]

/-! ## Completion modulo a power-torsion quotient -/

/- `I^c • Q = 0` is the module form of saying that `Q` is annihilated by a
   power of `I`. -/
theorem isAdicComplete_of_power_annihilated
    {R : Type u} [CommRing R] (I : Ideal R)
    {Q : Type v} [AddCommGroup Q] [Module R Q]
    (hQ : ∃ c : ℕ, I ^ c • (⊤ : Submodule R Q) = ⊥) :
    IsAdicComplete I Q := by
  rcases hQ with ⟨c, hc⟩
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · refine ⟨fun x hx => ?_⟩
    have hx' := hx c
    rw [hc, SModEq.bot] at hx'
    exact hx'
  · refine ⟨fun f hf => ⟨f c, ?_⟩⟩
    intro n
    by_cases h : n ≤ c
    · exact hf h
    · have hcn : c ≤ n := Nat.le_of_not_ge h
      have hle : I ^ n • (⊤ : Submodule R Q) ≤ ⊥ :=
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hcn)).trans hc.le
      have hzero : I ^ n • (⊤ : Submodule R Q) = ⊥ := le_antisymm hle bot_le
      have hfc := hf hcn
      rw [hc, SModEq.bot] at hfc
      rw [hzero, SModEq.bot]
      exact hfc.symm

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
  rcases hQ with ⟨c, hc⟩
  have hIc : I ^ c • (⊤ : Submodule R N) ≤ g.ker := by
    have hmap : Submodule.map g (I ^ c • (⊤ : Submodule R N)) =
        I ^ c • (⊤ : Submodule R Q) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    intro x hx
    have hx' : g x ∈ I ^ c • (⊤ : Submodule R Q) := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hx
    rw [hc] at hx'
    exact hx'
  have hpreimage (n : ℕ) {x : N}
      (hx : x ∈ I ^ (n + c) • (⊤ : Submodule R N))
      (hxker : x ∈ g.ker) :
      ∃ z : K, z ∈ I ^ n • (⊤ : Submodule R K) ∧ f z = x := by
    have hpow : I ^ (n + c) • (⊤ : Submodule R N) ≤
        I ^ n • g.ker := by
      rw [pow_add, Submodule.mul_smul]
      exact smul_mono_right _ hIc
    have hx' : x ∈ I ^ n • g.ker := hpow hx
    rw [hfg.linearMap_ker_eq, LinearMap.range_eq_map] at hx'
    have hmapf : I ^ n • Submodule.map f (⊤ : Submodule R K) =
        Submodule.map f (I ^ n • (⊤ : Submodule R K)) := by
      rw [Submodule.map_smul'', Submodule.map_top]
    rw [hmapf] at hx'
    exact (Submodule.mem_map (f := f) (p := I ^ n • (⊤ : Submodule R K))
      (x := x)).1 hx'
  have hinj : Function.Injective (AdicCompletion.map I f) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x
    apply AdicCompletion.induction_on I K x (fun a ↦ ?_)
    intro hx
    refine AdicCompletion.mk_zero_of I K a ⟨0, fun n _ ↦ ?_⟩
    have hcoord := congrArg (fun z => z.val (n + c)) hx
    have hcoord' : Submodule.Quotient.mk
        (p := I ^ (n + c) • (⊤ : Submodule R N)) (f (a (n + c))) = 0 := by
      simpa [AdicCompletion.map_val_apply] using hcoord
    have hfa : f (a (n + c)) ∈ I ^ (n + c) • (⊤ : Submodule R N) :=
      (Submodule.Quotient.mk_eq_zero _).mp hcoord'
    have hgker : f (a (n + c)) ∈ g.ker := by
      exact congrArg (fun k => k (a (n + c))) hfg.linearMap_comp_eq_zero
    obtain ⟨z, hz, hzf⟩ := hpreimage n hfa hgker
    have hza : z = a (n + c) := hf (by simpa [hzf])
    exact ⟨n + c, by omega, n, by omega, hza ▸ hz⟩
  have hexact_map : Function.Exact
      ((AdicCompletion.map I f).restrictScalars R :
        completion I K →ₗ[R] completion I N)
      ((AdicCompletion.map I g).restrictScalars R) := by
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range
    · apply LinearMap.ext
      intro x
      change AdicCompletion.map I g (AdicCompletion.map I f x) = 0
      rw [← LinearMap.comp_apply, AdicCompletion.map_comp,
        hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
      rfl
    · intro y
      apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
      intro hb
      have hgb (n : ℕ) : g (b (n + c)) ∈ I ^ (n + c) • (⊤ : Submodule R Q) := by
        have hcoord := congrArg (fun z => z.val (n + c)) (LinearMap.mem_ker.mp hb)
        have hq : Submodule.Quotient.mk
            (p := I ^ (n + c) • (⊤ : Submodule R Q)) (g (b (n + c))) = 0 := by
          simpa [AdicCompletion.map_val_apply] using hcoord
        exact (Submodule.Quotient.mk_eq_zero _).mp hq
      choose a ha using fun n => by
        have hzero : I ^ (n + c) • (⊤ : Submodule R Q) = ⊥ := by
          apply le_antisymm
          · exact (Submodule.smul_mono_left
              (Ideal.pow_le_pow_right (show c ≤ n + c by omega))).trans hc.le
          · exact bot_le
        have hgzero : g (b (n + c)) = 0 := by
          have hmem := hgb n
          rw [hzero] at hmem
          exact hmem
        exact (hfg (b (n + c))).mp hgzero
      have ha_cauchy : ∀ n, a n ≡ a (n + 1)
          [SMOD (I ^ n • (⊤ : Submodule R K))] := by
        intro n
        rw [SModEq.sub_mem]
        have hbdiff : b (n + 1 + c) - b (n + c) ∈
            I ^ (n + c) • (⊤ : Submodule R N) :=
          SModEq.sub_mem.mp (b.property (show n + c ≤ n + 1 + c by omega)).symm
        have hdiff : f (a (n + 1) - a n) =
            b (n + 1 + c) - b (n + c) := by
          rw [map_sub, ha (n + 1), ha n]
        have hdiff' : f (a (n + 1) - a n) ∈
            I ^ (n + c) • (⊤ : Submodule R N) := by
          rw [hdiff]
          exact hbdiff
        have hdiffker : f (a (n + 1) - a n) ∈ g.ker := by
          exact congrArg (fun k => k (a (n + 1) - a n)) hfg.linearMap_comp_eq_zero
        obtain ⟨z, hz, hzf⟩ := hpreimage n hdiff' hdiffker
        have hza : z = a (n + 1) - a n := hf (by simpa [hzf])
        have hneg : -z ∈ I ^ n • (⊤ : Submodule R K) := Submodule.neg_mem _ hz
        simpa [hza] using hneg
      let aa := AdicCompletion.AdicCauchySequence.mk I K a ha_cauchy
      refine ⟨AdicCompletion.mk I K aa, ?_⟩
      ext n
      change Submodule.Quotient.mk (f (a n)) = Submodule.Quotient.mk (b n)
      rw [ha n]
      exact AdicCompletion.AdicCauchySequence.mk_eq_mk
        (show n ≤ n + c by omega) b
  have hexact_comp : Function.Exact (AdicCompletion.map I f)
      (completionMapToPowerAnnihilated I g ⟨c, hc⟩) := by
    change Function.Exact
      ((AdicCompletion.map I f).restrictScalars R :
        completion I K →ₗ[R] completion I N)
      ((completionToPowerAnnihilated I Q ⟨c, hc⟩).toLinearMap ∘ₗ
        (AdicCompletion.map I g).restrictScalars R)
    apply LinearMap.exact_of_comp_eq_zero_of_ker_le_range
    · apply LinearMap.ext
      intro x
      change (completionToPowerAnnihilated I Q ⟨c, hc⟩)
          (AdicCompletion.map I g (AdicCompletion.map I f x)) = 0
      have hzero : AdicCompletion.map I g (AdicCompletion.map I f x) = 0 := by
        rw [← LinearMap.comp_apply, AdicCompletion.map_comp,
          hfg.linearMap_comp_eq_zero, AdicCompletion.map_zero]
        rfl
      rw [hzero]
      exact (completionToPowerAnnihilated I Q ⟨c, hc⟩).map_zero
    · intro y
      apply AdicCompletion.induction_on I N y (fun b ↦ ?_)
      intro hb
      have hb' : AdicCompletion.map I g (AdicCompletion.mk I N b) = 0 := by
        apply (completionToPowerAnnihilated I Q ⟨c, hc⟩).injective
        simpa [LinearMap.comp_apply] using hb
      exact (hexact_map (AdicCompletion.mk I N b)).mp hb'
  have hsurj_comp : Function.Surjective
      (completionMapToPowerAnnihilated I g ⟨c, hc⟩) := by
    exact (completionToPowerAnnihilated I Q ⟨c, hc⟩).surjective.comp
      (AdicCompletion.map_surjective I hg)
  exact ⟨hinj, hexact_comp, hsurj_comp⟩

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
  constructor
  · intro hM
    intro n hn
    apply le_antisymm
    intro x hx
    have hstep (m : ℕ) {z : completion I M}
        (hz : z ∈ completionKernel I M m) :
        ∃ y : completion I M, y ∈ completionKernel I M (m + 1) ∧
          z - y ∈ I ^ m • (⊤ : Submodule R (completion I M)) := by
      have hzval : z.val m = 0 := by
        exact LinearMap.mem_ker.mp hz
      have hmem : z.val (m + 1) ∈
          I ^ m • (⊤ : Submodule R (M ⧸ (I ^ (m + 1) • (⊤ : Submodule R M)))) :=
        (AdicCompletion.val_apply_mem_smul_top_iff (I := I) (M := M)
          (Nat.le_succ m)).2 hzval
      have hmap :
          Submodule.map (Submodule.mkQ (I ^ (m + 1) • (⊤ : Submodule R M)))
              (I ^ m • (⊤ : Submodule R M)) =
            I ^ m • (⊤ : Submodule R (M ⧸ (I ^ (m + 1) • (⊤ : Submodule R M)))) := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      rw [← hmap] at hmem
      obtain ⟨a, ha, haz⟩ := (Submodule.mem_map
        (f := Submodule.mkQ (I ^ (m + 1) • (⊤ : Submodule R M)))
        (p := I ^ m • (⊤ : Submodule R M)) (x := z.val (m + 1))).1 hmem
      refine ⟨z - AdicCompletion.of I M a, ?_, ?_⟩
      · rw [LinearMap.mem_ker, AdicCompletion.eval_apply,
          AdicCompletion.val_sub_apply, AdicCompletion.of_apply, haz]
        simp
      · have hofa : AdicCompletion.of I M a ∈
            I ^ m • (⊤ : Submodule R (completion I M)) := by
          have hmapof : Submodule.map (AdicCompletion.of I M)
                (I ^ m • (⊤ : Submodule R M)) ≤
              I ^ m • (⊤ : Submodule R (completion I M)) := by
            rw [Submodule.map_smul'', Submodule.map_top]
            exact smul_mono_right _ le_top
          exact hmapof (Submodule.mem_map_of_mem ha)
        convert hofa using 1 <;> abel
    let next (j : ℕ)
        (z : {z : completion I M // z ∈ completionKernel I M (n + j)}) :
        {z : completion I M // z ∈ completionKernel I M (n + j + 1)} := by
      let h := hstep (n + j) z.property
      exact ⟨h.choose, h.choose_spec.1⟩
    have hnext (j : ℕ)
        (z : {z : completion I M // z ∈ completionKernel I M (n + j)}) :
        z.1 - (next j z).1 ∈ I ^ (n + j) • (⊤ : Submodule R (completion I M)) := by
      dsimp [next]
      exact (hstep (n + j) z.property).choose_spec.2
    let cseq : (j : ℕ) →
        {z : completion I M // z ∈ completionKernel I M (n + j)} :=
      Nat.rec ⟨x, by simpa using hx⟩ (fun j z => next j z)
    have hcstep (j : ℕ) :
        (cseq j).1 - (cseq (j + 1)).1 ∈
          I ^ (n + j) • (⊤ : Submodule R (completion I M)) := by
      simpa [cseq] using hnext j (cseq j)
    have hcchain : ∀ {j l : ℕ}, j ≤ l →
        (cseq j).1 - (cseq l).1 ∈
          I ^ (n + j) • (⊤ : Submodule R (completion I M)) := by
      intro j l hjl
      induction l, hjl using Nat.le_induction with
      | base => simp
      | succ l hle ih =>
          have hmon : I ^ (n + l) • (⊤ : Submodule R (completion I M)) ≤
              I ^ (n + j) • (⊤ : Submodule R (completion I M)) :=
            Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
          have hlast := hmon (hcstep l)
          convert Submodule.add_mem _ ih hlast using 1 <;> abel
    have hcx (j : ℕ) :
        x - (cseq j).1 ∈ I ^ n • (⊤ : Submodule R (completion I M)) := by
      simpa [cseq] using hcchain (j := 0) (l := j) (Nat.zero_le j)
    let b (k : ℕ) : completion I M :=
      if hkn : k ≤ n then x else (cseq (k - n)).1
    have hbK (k : ℕ) : b k ∈ completionKernel I M k := by
      by_cases hkn : k ≤ n
      · simp only [b, dif_pos hkn]
        have hprop := x.property hkn
        have hxval : x.val n = 0 := LinearMap.mem_ker.mp hx
        rw [hxval] at hprop
        rw [LinearMap.mem_ker, AdicCompletion.eval_apply]
        simpa using hprop.symm
      · simp only [b, dif_neg hkn]
        have hnle : n ≤ k := Nat.le_of_not_ge hkn
        simpa [Nat.add_sub_of_le hnle] using (cseq (k - n)).property
    have hb_cauchy : ∀ {m k : ℕ}, m ≤ k →
        b m ≡ b k [SMOD (I ^ m • (⊤ : Submodule R (completion I M)))] := by
      intro m k hmk
      rw [SModEq.sub_mem]
      by_cases hkn : k ≤ n
      · have hmn : m ≤ n := hmk.trans hkn
        simp only [b]
        rw [dif_pos hmn, dif_pos hkn]
        simpa using (Submodule.zero_mem (I ^ m • (⊤ : Submodule R (completion I M))))
      · have hnle : n ≤ k := Nat.le_of_not_ge hkn
        by_cases hmn : m ≤ n
        · have hmon : I ^ n • (⊤ : Submodule R (completion I M)) ≤
              I ^ m • (⊤ : Submodule R (completion I M)) :=
            Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
          have hmem := hmon (hcx (k - n))
          simp only [b]
          rw [dif_pos hmn, dif_neg hkn]
          exact hmem
        · have hmn' : n < m := Nat.lt_of_not_ge hmn
          have hchain := hcchain (j := m - n) (l := k - n) (by omega)
          simp only [b]
          rw [dif_neg hmn, dif_neg hkn]
          simpa [Nat.add_sub_of_le (Nat.le_of_lt hmn')] using hchain
    obtain ⟨L, hL⟩ := hM.toIsPrecomplete.prec' b hb_cauchy
    have hLzero : L = 0 := by
      apply AdicCompletion.ext
      intro k
      have hdiff := SModEq.sub_mem.mp (hL k)
      have hdiffK : b k - L ∈ completionKernel I M k :=
        (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) k) hdiff
      have hLK : L ∈ completionKernel I M k := by
        have hsub := (completionKernel I M k).sub_mem (hbK k) hdiffK
        convert hsub using 1 <;> abel
      simpa [AdicCompletion.eval_apply] using LinearMap.mem_ker.mp hLK
    have hnconv := SModEq.sub_mem.mp (hL n)
    have hxn : x ∈ I ^ n • (⊤ : Submodule R (completion I M)) := by
      have hbn : b n = x := by simp [b]
      rw [hbn, hLzero] at hnconv
      simpa using hnconv
    exact hxn
    · simpa [completionKernel] using
        (AdicCompletion.pow_smul_top_le_ker_eval (I := I) (M := M) n)
  · intro hall
    have hpow (n : ℕ) : I ^ n • (⊤ : Submodule R (completion I M)) =
        (AdicCompletion.eval I M n).ker := by
      by_cases hn : 1 ≤ n
      · exact (hall n hn).symm
      · have hn0 : n = 0 := by omega
        subst n
        rw [show I ^ 0 • (⊤ : Submodule R (completion I M)) = ⊤ by simp]
        apply le_antisymm
        · intro x hx
          rw [LinearMap.mem_ker, AdicCompletion.eval_apply]
          refine Quotient.inductionOn' (x.val 0) (fun z => ?_)
          exact (Submodule.Quotient.mk_eq_zero
            (I ^ 0 • (⊤ : Submodule R M))).2 (by simp)
        · exact le_top
    refine { toIsHausdorff := inferInstance, toIsPrecomplete := ?_ }
    refine ⟨?_⟩
    intro f hf
    let L : completion I M := {
      val i := (f i).val i
      property {m n} hmn := by
        simp only [AdicCompletion.transitionMap_comp_eval_apply]
        specialize hf hmn
        rw [SModEq.sub_mem, hpow m, LinearMap.mem_ker, _root_.map_sub,
          sub_eq_zero, AdicCompletion.eval_apply, AdicCompletion.eval_apply] at hf
        simpa only using hf.symm
    }
    refine ⟨L, ?_⟩
    intro i
    rw [SModEq.sub_mem, hpow i]
    rw [LinearMap.mem_ker, AdicCompletion.eval_apply]
    change (f i).val i - (f i).val i = 0
    exact sub_self _

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
