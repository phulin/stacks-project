import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 52: Length

Mathlib's `Module.length`, `IsFiniteLength`, `CompositionSeries`, and
`IsSimpleModule` are the canonical interfaces used throughout this section.
The source's localization notation is represented by `LocalizedModule`, and
the residue-degree factor in the semilocal statement is represented by the
corresponding length of the residue field as an `A`-module.
-/

namespace Formalization.Books.Algebra.Unit52

noncomputable section

open scoped BigOperators TensorProduct

/-! ## Length and finite-length modules -/

/- The source's supremum of chain lengths is Mathlib's `Module.length`, whose
   values are extended naturals.  The chain-refinement and equal-maximal-chain
   remarks are represented by the `CompositionSeries` interfaces below. -/

theorem finite_length_finite
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : Module.length R M < ⊤) :
    Module.Finite R M := by
  have hM' : Module.length R M ≠ ⊤ := ne_of_lt hM
  have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp hM'
  let _ : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).1
  infer_instance

theorem length_additive
    {R M' M M'' : Type*} [CommRing R]
    [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module R M'] [Module R M] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    Module.length R M = Module.length R M' + Module.length R M'' := by
  exact Module.length_eq_add_of_exact f g hf hg hfg

private theorem exists_maximalIdeal_pow_smul_top_eq_bot_of_isFiniteLength
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hfin : IsFiniteLength R M) :
    ∃ n : ℕ, (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M) = ⊥ := by
  let I : Ideal R := IsLocalRing.maximalIdeal R
  induction hfin with
  | of_subsingleton =>
      refine ⟨0, ?_⟩
      ext x
      simp [show x = 0 from Subsingleton.elim x 0]
  | @of_simple_quotient M _ _ N _ _ ih =>
      obtain ⟨n, hn⟩ := ih
      have hmax : (Module.annihilator R (M ⧸ N)).IsMaximal :=
        IsSimpleModule.annihilator_isMaximal
      have hquot' : (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        rw [← IsLocalRing.eq_maximalIdeal hmax, ← Submodule.annihilator_top,
          ← Submodule.le_annihilator_iff]
      have hquot : I • (⊤ : Submodule R (M ⧸ N)) = ⊥ := by
        simpa [I] using hquot'
      have hIN : I • (⊤ : Submodule R M) ≤ N := by
        rw [← N.ker_mkQ]
        apply LinearMap.le_ker_iff_map.mpr
        rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
          N.mkQ_surjective]
        exact hquot
      have hn' : I ^ n • N = ⊥ := by
        have h := congrArg (fun P : Submodule R N => P.map N.subtype) hn
        simpa only [Submodule.map_smul'', Submodule.map_subtype_top, Submodule.map_bot] using h
      refine ⟨n + 1, le_antisymm ?_ bot_le⟩
      rw [pow_succ, Submodule.mul_smul]
      exact (smul_mono_right (I ^ n) hIN).trans_eq hn'

theorem length_infinite_of_maximalIdeal_pow_smul_top_ne_bot
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hM : ∀ n : ℕ,
      (IsLocalRing.maximalIdeal R) ^ n • (⊤ : Submodule R M) ≠ ⊥) :
    Module.length R M = ⊤ := by
  by_contra htop
  have hfin : IsFiniteLength R M := Module.length_ne_top_iff.mp htop
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_smul_top_eq_bot_of_isFiniteLength hfin
  exact hM n hn

/- A ring map is represented directly, with the restricted scalar action
   supplied by `Module.compHom`. -/
theorem length_independent
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] (f : R →+* S) [Module S M] :
    @Module.length S M _ _ (inferInstance : Module S M) ≤
      @Module.length R M _ _ (Module.compHom M f) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  have h := Submodule.length_le_length_restrictScalars
    (R := S) (M := M) R (⊤ : Submodule S M)
  have htopR : (⊤ : Submodule S M).restrictScalars R = (⊤ : Submodule R M) := by
    ext x
    simp
  rw [htopR] at h
  simpa only [Module.length_top] using h

theorem length_eq_of_surjective_ringHom
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] (f : R →+* S) (hf : Function.Surjective f)
    [Module S M] :
    @Module.length R M _ _ (Module.compHom M f) =
      @Module.length S M _ _ (inferInstance : Module S M) := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Module R M := Module.compHom M f
  let _ : IsScalarTower R S M := IsScalarTower.of_compHom R S M
  simpa only [RingHom.algebraMap_toAlgebra] using
    (Module.length_eq_of_surjective (R := S) (S := R) (M := M) hf)

/- If an ideal annihilates `M`, Mathlib's `IsTorsionBySet.module` supplies the
   canonical module structure over the quotient ring. -/
theorem dimension_is_length
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) [m.IsMaximal]
    (hM : Module.IsTorsionBySet R M m) :
    letI := hM.module
    Module.length R M = (Module.rank (R ⧸ m) M).toENat ∧
      (Module.length R M < ⊤ ↔ Module.Finite R M) := by
  sorry

theorem length_localize
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    Module.length (Localization S) (LocalizedModule S M) ≤
      Module.length R M := by
  sorry

theorem length_finite_of_fg_maximalIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (hm : m.IsMaximal) (hm_fg : m.FG) [Module.Finite R M]
    (n : ℕ) (hpow : m ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.length R M < ⊤ := by
  sorry

/- The source's parenthetical Noetherian example is already supplied by
   `Ideal.fg_of_isNoetherianRing`, so this theorem keeps the stated FG
   hypothesis without introducing a parallel criterion. -/

/-! ## Simple modules and composition factors -/

/- The source's definition of a simple module is Mathlib's canonical
   `IsSimpleModule`. -/

theorem simple_iff_length_one_and_maximal_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] :
    (IsSimpleModule R M ↔ Module.length R M = 1) ∧
      (IsSimpleModule R M ↔
        ∃ m : Ideal R, m.IsMaximal ∧
          Nonempty (M ≃ₗ[R] R ⧸ m)) := by
  exact ⟨Module.length_eq_one_iff.symm, isSimpleModule_iff_quot_maximal⟩

/- A `CompositionSeries` is the canonical maximal chain used for the
   source's finite-length chain assertions. -/

theorem exists_maximal_chain_of_finite_length
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hM : IsFiniteLength R M) :
    ∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤ := by
  exact isFiniteLength_iff_exists_compositionSeries.mp hM

theorem maximal_chain_length
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M))
    (hs : s.head = ⊥) (ht : s.last = ⊤) :
    (s.length : ℕ∞) = Module.length R M := by
  exact Module.length_compositionSeries s hs ht

theorem compositionSeries_simple_factors
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M))
    (hs : s.head = ⊥) (ht : s.last = ⊤) :
    ∃ m : Fin s.length → Ideal R,
      ∀ i, IsSimpleModule R
          (s (Fin.succ i) ⧸
            Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))) ∧
        (m i).IsMaximal ∧
        Nonempty
          ((s (Fin.succ i) ⧸
              Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
            ≃ₗ[R] R ⧸ m i) := by
  sorry

theorem localized_residueField
    {R : Type*} [CommRing R] (m m' : Ideal R)
    [m.IsMaximal] [m'.IsMaximal] :
    (m ≠ m' →
      Nonempty
        (LocalizedModule.AtPrime m (R ⧸ m') ≃ₗ[Localization.AtPrime m]
          (⊥ : Submodule (Localization.AtPrime m) (Localization.AtPrime m)))) ∧
      (m = m' →
        Nonempty
          (LocalizedModule.AtPrime m (R ⧸ m') ≃ₗ[Localization.AtPrime m]
            Localization.AtPrime m ⧸
              m.map (algebraMap R (Localization.AtPrime m)))) := by
  sorry

theorem compositionSeries_localized_multiplicity
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M))
    (hs : s.head = ⊥) (ht : s.last = ⊤)
    (m : Fin s.length → Ideal R)
    (hm : ∀ i, (m i).IsMaximal)
    (hfactor :
      ∀ i,
        Nonempty
          ((s (Fin.succ i) ⧸
              Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
            ≃ₗ[R] R ⧸ m i))
    (m₀ : Ideal R) [m₀.IsMaximal] :
    (Nat.card {i : Fin s.length // m i = m₀} : ℕ∞) =
      Module.length (Localization.AtPrime m₀)
        (LocalizedModule.AtPrime m₀ M) := by
  sorry

/-! ## Restriction along local maps -/

/- The source enumerates the maximal ideals of a semilocal ring.  The
   canonical finite type `MaximalSpectrum B` is used instead, so the sum is
   independent of a chosen enumeration. -/
theorem length_pushdown
    {A B M : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [Algebra A B] [AddCommGroup M] [Module B M] [Module A M]
    [IsScalarTower A B M] [Finite (MaximalSpectrum B)]
    (h_over :
      ∀ q : MaximalSpectrum B,
        q.asIdeal.comap (algebraMap A B) = IsLocalRing.maximalIdeal A)
    (hfinite :
      ∀ q : MaximalSpectrum B, Module.Finite A q.asIdeal.ResidueField)
    (hM : IsFiniteLength B M) :
    letI := Fintype.ofFinite (MaximalSpectrum B)
    Module.length A M =
        ∑ q : MaximalSpectrum B,
          Module.length A q.asIdeal.ResidueField *
            Module.length (Localization.AtPrime q.asIdeal)
              (LocalizedModule.AtPrime q.asIdeal M) ∧
      Module.length A M < ⊤ := by
  sorry

theorem length_pullback
    {A B M : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)] :
    Module.length B (B ⊗[A] M) =
      Module.length A M *
        Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) := by
  exact IsLocalRing.length_baseChange A B M

theorem finite_length_pullback_iff
    {A B M : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)]
    (hB :
      Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) < ⊤) :
    Module.length A M < ⊤ ↔ Module.length B (B ⊗[A] M) < ⊤ := by
  sorry

theorem length_pullback_transitive
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [IsLocalRing A] [IsLocalRing B] [IsLocalRing C]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C]
    [Module.Flat A B] [Module.Flat B C]
    [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap B C)] :
    Module.length B
        (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) *
        Module.length C
          (C ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B C)) =
      Module.length C
        (C ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A C)) := by
  sorry

end

end Formalization.Books.Algebra.Unit52
