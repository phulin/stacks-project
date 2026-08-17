import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Jacobson.Ideal

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
  sorry

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
  sorry

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
  sorry

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
