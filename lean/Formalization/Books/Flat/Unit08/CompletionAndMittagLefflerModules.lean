import Formalization.Books.Algebra.Unit65.RelativeAssassin
import Formalization.Books.Algebra.Unit91.ExamplesAndNonExamples
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.MoreAlgebra.Unit28.CompletionFlatness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# More on Flatness, Chapter 8: Completion and Mittag-Leffler modules

The source's module completions are Mathlib's `AdicCompletion`s.  The
Mittag-Leffler predicate is the established `IsMittagLefflerModule`, and
universal injectivity is the tensor criterion from Algebra, Chapter 82.
The source writes `Q ⊗_R N` in the associated-prime conditions.  We use the
canonically symmetric `N ⊗[R] Q` orientation so that the existing S-module
structure on `N` supplies the S-action on the tensor product.
-/

namespace Formalization.Books.Flat.Unit08

open CategoryTheory
open Formalization.Books.Algebra.Unit82
open Formalization.Books.Algebra.Unit88
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit97
open Formalization.Books.MoreAlgebra.Unit28
open scoped DirectSum TensorProduct

universe u v w z

noncomputable section

private theorem mittagLeffler_of_universallyInjective
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : universallyInjective f)
    (hN : IsMittagLefflerModule (ModuleCat.of R N)) :
    IsMittagLefflerModule (ModuleCat.of R M) := by
  let q : N →ₗ[R] (N ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  have hshort : Function.Injective f ∧ Function.Exact f q ∧
      Function.Surjective q := by
    exact ⟨(LinearMap.range f).injective_subtype, f.exact_map_mkQ_range,
      Submodule.mkQ_surjective _⟩
  have hseq : universallyExact f q := by
    refine ⟨hshort.1, hshort.2.1, hshort.2.2, hf⟩
  exact (pure_submodule_mittagLeffler f q hseq).1 hN

private theorem mittagLeffler_of_split
    {R : Type u} {M N : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : s.comp f = LinearMap.id)
    (hN : IsMittagLefflerModule (ModuleCat.of R N)) :
    IsMittagLefflerModule (ModuleCat.of R M) := by
  let q : N →ₗ[R] (N ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => s z) hxy
    simpa [LinearMap.comp_apply, hs] using this
  have hshort : Function.Injective f ∧ Function.Exact f q ∧
      Function.Surjective q := by
    exact ⟨hinj, f.exact_map_mkQ_range, Submodule.mkQ_surjective _⟩
  have hseq : universallyExact f q := by
    refine ⟨hshort.1, hshort.2.1, hshort.2.2, ?_⟩
    intro Q _ _ x y hxy
    have h := congrArg (fun z => (s.rTensor Q) z) hxy
    simpa [LinearMap.rTensor, TensorProduct.map_map, hs] using h
  exact (pure_submodule_mittagLeffler f q hseq).1 hN

private theorem range_rTensor_smul_top
    {R : Type u} {N : Type v} {Q : Type w} [CommRing R]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    (J : Ideal R) :
    LinearMap.range ((J • (⊤ : Submodule R N)).subtype.rTensor Q) =
      J • (⊤ : Submodule R (N ⊗[R] Q)) := by
  apply le_antisymm
  · rintro z ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa [map_add] using add_mem hx hy
    | tmul x q =>
        refine Submodule.smul_induction_on x.property ?_ ?_
        · intro r hr n hn
          simpa [smul_tmul] using
            Submodule.smul_mem_smul hr
              (show n ⊗ₜ[R] q ∈ (⊤ : Submodule R (N ⊗[R] Q)) by simp)
        · intro x y hx hy
          simpa [add_tmul] using add_mem hx hy
  · intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro r hr x hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simpa [smul_add] using add_mem hx hy
      | tmul n q =>
          let n' : J • (⊤ : Submodule R N) :=
            ⟨r • n, Submodule.smul_mem_smul hr (by simp)⟩
          refine ⟨n' ⊗ₜ[R] q, ?_⟩
          simp [n', smul_tmul]
    · intro x y hx hy
      simpa using Submodule.add_mem _ hx hy

private theorem hausdorff_of_associatedPrimes
    {S : Type u} {M : Type v} [CommRing S] [IsNoetherianRing S]
    [AddCommGroup M] [Module S M] [Module.Finite S M]
    (J : Ideal S)
    (hJ : ∀ q ∈ _root_.associatedPrimes S M,
      J + q ≠ (⊤ : Ideal S)) :
    IsHausdorff J M := by
  rw [isHausdorff_iff]
  intro x hx
  have hxinf : x ∈ (⨅ n : ℕ, J ^ n • (⊤ : Submodule S M)) := by
    rw [Submodule.mem_iInf]
    intro n
    exact SModEq.zero.mp (hx n)
  obtain ⟨r, hrx⟩ := (J.mem_iInf_smul_pow_eq_bot_iff x).mp hxinf
  have hreg : IsSMulRegular M (1 - (r : S)) := by
    have hnot : (1 - (r : S)) ∉
        ⋃ q ∈ _root_.associatedPrimes S M, q := by
      intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨q, hmem⟩
      rcases Set.mem_iUnion.mp hmem with ⟨hq, hmem⟩
      apply hJ q hq
      rw [Ideal.eq_top_iff_one]
      simpa using Ideal.add_mem _ r.property hmem
    have hnot' : (1 - (r : S)) ∉
        {s : S | IsSMulRegular M s}ᶜ := by
      rw [← biUnion_associatedPrimes_eq_compl_regular S M]
      exact hnot
    simpa using hnot'
  exact hreg.right_eq_zero_of_smul (by
    rw [sub_smul, one_smul, hrx]
    exact sub_self x)

private theorem finite_tensorProduct_left
    {R : Type u} {S : Type v} {N : Type w} {Q : Type z}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N]
    [IsScalarTower R S N] [AddCommGroup Q] [Module R Q]
    [Module.Finite S N] [Module.Finite R Q] :
    letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
    Module.Finite S (N ⊗[R] Q) := by
  letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite S N).fg_top
  obtain ⟨t, ht⟩ := (inferInstance : Module.Finite R Q).fg_top
  let U : Finset (N ⊗[R] Q) :=
    (s.product t).image (fun x => x.1 ⊗ₜ[R] x.2)
  refine ⟨⟨U, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul n q =>
      have hn : n ∈ Submodule.span S (s : Set N) := by
        rw [hs]
        exact Submodule.mem_top
      have hq : q ∈ Submodule.span R (t : Set Q) := by
        rw [ht]
        exact Submodule.mem_top
      refine Submodule.span_induction (R := S) ?_ ?_ ?_ ?_ hn
      · intro n hn
        refine Submodule.span_induction (R := R) ?_ ?_ ?_ ?_ hq
        · intro q hq
          apply Submodule.subset_span
          exact Finset.mem_image.mpr ⟨(n, q), Finset.mem_product.mpr ⟨hn, hq⟩, rfl⟩
        · simp
        · intro q₁ q₂ _ _ hq₁ hq₂
          simpa [tmul_add] using Submodule.add_mem _ hq₁ hq₂
        · intro r q _ hq
          simpa [tmul_smul, ← IsScalarTower.algebraMap_smul S r n] using
            Submodule.smul_mem _ (algebraMap R S r) hq
      · simp
      · intro n₁ n₂ _ _ hn₁ hn₂
        simpa [add_tmul] using Submodule.add_mem _ hn₁ hn₂
      · intro a n _ hn
        simpa [TensorProduct.smul_tmul'] using Submodule.smul_mem _ a hn

/-! ## Completion and Mittag-Leffler modules -/

/-- The completion of an arbitrary direct sum of copies of a complete
Noetherian ring is flat and Mittag-Leffler. -/
theorem completedDirectSum_flat_and_mittagLeffler
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (A : Type v) :
    Module.Flat R (completion I (⨁ _ : A, R)) ∧
      IsMittagLefflerModule
        (ModuleCat.of R (completion I (⨁ _ : A, R))) := by
  refine ⟨completedDirectSum_flat I A, ?_⟩
  apply mittagLeffler_of_universallyInjective
    (completedDirectSumToProduct I A)
    (completedDirectSumToProduct_universallyInjective I A)
  simpa [Formalization.Books.Algebra.Unit89.modulePower] using
    (Formalization.Books.Algebra.Unit91.modulePower_is_flat_and_mittagLeffler R A).2

/-- The completion of a flat module whose reduction is projective is flat and
Mittag-Leffler over a complete Noetherian ring. -/
theorem completion_flat_and_mittagLeffler_of_flat_of_projective_mod
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Flat R M]
    [Module.Projective (R ⧸ I)
      (M ⧸ (I • (⊤ : Submodule R M)))] :
      Module.Flat R (completion I M) ∧
      IsMittagLefflerModule (ModuleCat.of R (completion I M)) := by
  let F : Type max u v := M →₀ R
  let g : F →ₗ[R] M := Finsupp.linearCombination R (id : M → M)
  have hg : Function.Surjective g := by
    dsimp [g, F]
    simpa using (Finsupp.linearCombination_id_surjective R M)
  have hsplit := completion_split_exact I (LinearMap.ker g).subtype g
    (LinearMap.ker g).injective_subtype
    (LinearMap.exact_subtype_ker_map g) hg
  obtain ⟨_, _, _, ⟨s, hs⟩⟩ := hsplit
  let fR : completion I F →ₗ[R] completion I M :=
    (AdicCompletion.map I g).restrictScalars R
  let sR : completion I M →ₗ[R] completion I F := s.restrictScalars R
  have hsR : fR.comp sR = LinearMap.id := by
    ext x
    exact congrArg (fun h => h x) hs
  have hMLF : IsMittagLefflerModule
      (ModuleCat.of R (completion I F)) := by
    simpa [F, Formalization.Books.Algebra.Unit89.modulePower] using
      (completedDirectSum_flat_and_mittagLeffler (R := R) I M).2
  refine ⟨?_, mittagLeffler_of_split sR fR hsR hMLF⟩
  exact Module.Flat.of_retract (f := completedDirectSum_flat I M) sR fR hsR

/- The source's intervening finite-type remark is already represented by the
canonical `Formalization.Books.Algebra.Unit31.finiteType_algebra_isNoetherian`.
Its `[Algebra R S]` and `[Algebra.FiniteType R S]` interface is the standard
Lean form of a finite-type ring map, so no parallel chapter-local theorem is
needed here. -/

/-- The map into completion is universally injective under the associated-prime
condition tested after tensoring with every finite R-module. -/
theorem universallyInjective_to_completion
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [AddCommGroup N] [Module S N]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S N]
    (I : Ideal R) (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    (∀ (Q : Type z) [AddCommGroup Q] [Module R Q] [Module.Finite R Q],
      letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
      ∀ q ∈ _root_.associatedPrimes S (N ⊗[R] Q),
        I.map f + q ≠ (⊤ : Ideal S)) →
      universallyInjective (AdicCompletion.of I N) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := SMul.comp.isScalarTower f
  intro h
  letI : Module S (N ⊗[R] R) := TensorProduct.leftModule
  letI : Module.Finite S (N ⊗[R] R) :=
    finite_tensorProduct_left (R := R) (S := S) (N := N) (Q := R)
  letI : IsHausdorff (I.map f) (N ⊗[R] R) :=
    hausdorff_of_associatedPrimes (I.map f) (h R)
  have hHausR : IsHausdorff I (N ⊗[R] R) :=
    IsHausdorff.of_map (I := I) (J := I.map f) (by rfl)
  letI : IsHausdorff I (N ⊗[R] R) := hHausR
  have hNQR : Function.Injective (AdicCompletion.of I (N ⊗[R] R)) :=
    AdicCompletion.of_injective_iff.mpr hHausR
  have hinj : Function.Injective (AdicCompletion.of I N) := by
    intro x y hxy
    apply (TensorProduct.rid R N).injective
    apply hNQR
    apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
    intro n
    rw [SModEq.sub_mem]
    have hcoord := congrArg (AdicCompletion.eval I N n) hxy
    have hcoord' :
        ((I ^ n • (⊤ : Submodule R N)).mkQ) x =
          ((I ^ n • (⊤ : Submodule R N)).mkQ) y := by
      simpa [AdicCompletion.eval_of] using hcoord
    have hzero :
        ((I ^ n • (⊤ : Submodule R N)).mkQ) (x - y) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hcoord'
    have hmem : x - y ∈ I ^ n • (⊤ : Submodule R N) :=
      (Submodule.Quotient.mk_eq_zero _).mp hzero
    rw [← range_rTensor_smul_top]
    refine ⟨⟨x - y, hmem⟩ ⊗ₜ[R] (1 : R), ?_⟩
    simp
  let q : completion I N →ₗ[R]
      (completion I N ⧸ LinearMap.range (AdicCompletion.of I N)) :=
    (LinearMap.range (AdicCompletion.of I N)).mkQ
  have hshort : Function.Injective (AdicCompletion.of I N) ∧
      Function.Exact (AdicCompletion.of I N) q ∧ Function.Surjective q := by
    exact ⟨hinj, (AdicCompletion.of I N).exact_map_mkQ_range,
      Submodule.mkQ_surjective _⟩
  have hcrit := universallyExact_criteria (AdicCompletion.of I N) q hshort
  have hpost := hcrit.out 0 1
  refine (hpost.mpr ?_).2.2.2
  intro Q _ _
  letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
  letI : Module.Finite S (N ⊗[R] Q) :=
    finite_tensorProduct_left (R := R) (S := S) (N := N) (Q := Q)
  letI : IsHausdorff (I.map f) (N ⊗[R] Q) :=
    hausdorff_of_associatedPrimes (I.map f) (h Q)
  have hHausQ : IsHausdorff I (N ⊗[R] Q) :=
    IsHausdorff.of_map (I := I) (J := I.map f) (by rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    have hzero : x - y = 0 := hHausQ.haus (x - y) (fun n => by
      have hcoord := congrArg
        (fun z => (AdicCompletion.eval I N n).rTensor Q z) hxy
      have hcoord' :
          ((I ^ n • (⊤ : Submodule R N)).mkQ.rTensor Q) x =
            ((I ^ n • (⊤ : Submodule R N)).mkQ.rTensor Q) y := by
        simpa [← LinearMap.rTensor_comp_apply, AdicCompletion.eval_comp_of] using hcoord
      have hcoord'' :
          ((I ^ n • (⊤ : Submodule R N)).mkQ.rTensor Q) (x - y) = 0 := by
        simpa [map_sub] using sub_eq_zero.mpr hcoord'
      have hrange : x - y ∈ LinearMap.range
          ((I ^ n • (⊤ : Submodule R N)).subtype.rTensor Q) := by
        rw [← rTensor_mkQ Q (I ^ n • (⊤ : Submodule R N))]
        exact LinearMap.mem_ker.mpr hcoord''
      rw [range_rTensor_smul_top] at hrange
      exact SModEq.zero.mpr hrange)
    exact sub_eq_zero.mp hzero
  · exact rTensor_exact Q (AdicCompletion.of I N).exact_map_mkQ_range
      (Submodule.mkQ_surjective _)
  · exact LinearMap.rTensor_surjective Q (Submodule.mkQ_surjective _)

/-- The flat variant of universal injectivity, with the associated-prime
condition checked on the fibres over the contractions of primes of S. -/
theorem universallyInjective_to_completion_of_flat
    {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [AddCommGroup N] [Module S N]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S N]
    (I : Ideal R) (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    letI : Module R N := Module.compHom N f
    letI : IsScalarTower R S N := SMul.comp.isScalarTower f
    Module.Flat R N →
      (∀ (q : Ideal S) [q.IsPrime],
        letI : Module S (N ⊗[R] (q.comap f).ResidueField) :=
          TensorProduct.leftModule
        q ∈ _root_.associatedPrimes S
            (N ⊗[R] (q.comap f).ResidueField) →
          I.map f + q ≠ (⊤ : Ideal S)) →
      universallyInjective (AdicCompletion.of I N) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module R N := Module.compHom N f
  letI : IsScalarTower R S N := SMul.comp.isScalarTower f
  intro hflat hfib
  apply universallyInjective_to_completion I f
  intro Q _ _
  letI : Module S (N ⊗[R] Q) := TensorProduct.leftModule
  intro q hq
  have hbridge :=
    Formalization.Books.Algebra.Unit63.associatedPrimes_toIdeal_eq_mathlib
      (R := S) (M := N ⊗[R] Q)
  have hqimage : q ∈
      (fun p : PrimeSpectrum S => p.asIdeal) ''
        Formalization.Books.Algebra.Unit63.associatedPrimes S
          (N ⊗[R] Q) := by
    rw [hbridge]
    exact hq
  obtain ⟨q', hq', hqeq⟩ := hqimage
  have hB : q' ∈
      Formalization.Books.Algebra.Unit65.relativeAssassinB
        (R := R) (S := S) (N := N) := by
    refine ⟨Q, inferInstance, inferInstance, ?_⟩
    exact hq'
  have hAeqB :=
    Formalization.Books.Algebra.Unit65.relative_assassins_all_eq_of_noetherian_of_flat
      (R := R) (S := S) (N := N) hflat
  have hA : q' ∈
      Formalization.Books.Algebra.Unit65.relativeAssassinA
        (R := R) (S := S) (N := N) := by
    rw [hAeqB.1]
    exact hB
  have hA' : q' ∈
      Formalization.Books.Algebra.Unit63.associatedPrimes S
        (N ⊗[R] (q'.asIdeal.comap f).ResidueField) := by
    simpa [Formalization.Books.Algebra.Unit65.relativeAssassinA] using hA
  have hbridge' :=
    Formalization.Books.Algebra.Unit63.associatedPrimes_toIdeal_eq_mathlib
      (R := S) (M := N ⊗[R] (q'.asIdeal.comap f).ResidueField)
  have hAroot : q'.asIdeal ∈
      _root_.associatedPrimes S
        (N ⊗[R] (q'.asIdeal.comap f).ResidueField) := by
    rw [← hbridge']
    exact ⟨q', hA', rfl⟩
  simpa [hqeq] using hfib q'.asIdeal hAroot

end

end Formalization.Books.Flat.Unit08
