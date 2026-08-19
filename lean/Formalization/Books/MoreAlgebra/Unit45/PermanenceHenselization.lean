import Formalization.Books.MoreAlgebra.Unit44
import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit72.Depth
import Formalization.Books.Algebra.Unit97.CompletionForNoetherianRings
import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Formalization.Books.Algebra.Unit155.Henselization
import Formalization.Books.MoreAlgebra.Unit37.FormallySmooth
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# More Algebra, Chapter 45: Permanence of properties under henselization

The chosen henselization and strict henselization use
StrictHenselizationData from Algebra, Chapter 155. Completions use the
canonical adic-completion interface from the earlier algebra chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit45

open Formalization.Books.Algebra.Unit155
open Formalization.Books.Algebra.Unit154
open scoped TensorProduct

noncomputable section
universe u

instance strictDataHenselizationCommRing
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) : CommRing D.henselization :=
  D.commRingHenselization

instance strictDataHenselizationLocalRing
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) : IsLocalRing D.henselization :=
  D.localRingHenselization

instance strictDataStrictHenselizationCommRing
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) : CommRing D.strictHenselization :=
  D.commRingStrictHenselization

instance strictDataStrictHenselizationLocalRing
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) : IsLocalRing D.strictHenselization :=
  D.localRingStrictHenselization

def IsFreeOn
    (S M ι : Type u) [Semiring S] [AddCommMonoid M] [Module S M]
    (v : ι → M) : Prop :=
  ∃ b : Module.Basis ι S M, ∀ i, b i = v i

noncomputable def ResidueFieldExtensionIsSeparableAlgebraic
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hq : q.asIdeal.comap f = p.asIdeal) : Prop :=
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal f hq.symm).toAlgebra
  Algebra.IsAlgebraic p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
    Algebra.IsSeparable p.asIdeal.ResidueField q.asIdeal.ResidueField

theorem henselization_basic_properties
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    RingHom.FaithfullyFlat D.henselizationMap ∧
    RingHom.FaithfullyFlat D.mapFromHenselization ∧
    RingHom.FaithfullyFlat D.strictMap ∧
    Ideal.map D.henselizationMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal D.henselization ∧
    Ideal.map D.mapFromHenselization
        (IsLocalRing.maximalIdeal D.henselization) =
      IsLocalRing.maximalIdeal D.strictHenselization ∧
    Ideal.map D.strictMap (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal D.strictHenselization ∧
    (∀ n : ℕ,
      Function.Bijective
        (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap
          D.henselizationMap ((IsLocalRing.maximalIdeal R) ^ n))) ∧
    ∃ (ι : Type u) (x : ι → D.strictHenselization),
      ∀ n : ℕ,
        letI : Algebra
            (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)
            (D.strictHenselization ⧸
              Ideal.map D.strictMap ((IsLocalRing.maximalIdeal R) ^ n)) :=
          (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap
            D.strictMap ((IsLocalRing.maximalIdeal R) ^ n)).toAlgebra
        IsFreeOn
          (R ⧸ (IsLocalRing.maximalIdeal R) ^ n)
          (D.strictHenselization ⧸
            Ideal.map D.strictMap ((IsLocalRing.maximalIdeal R) ^ n)) ι
          (fun i => Ideal.Quotient.mk _ (x i)) := by
  sorry

theorem henselization_formally_etale_and_formally_smooth
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    (@Algebra.FormallyEtale R D.henselization _ _
        D.henselizationMap.toAlgebra) ∧
    (@Algebra.FormallyEtale D.henselization D.strictHenselization _ _
        D.mapFromHenselization.toAlgebra) ∧
    (@Algebra.FormallyEtale R D.strictHenselization _ _
        D.strictMap.toAlgebra) ∧
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      D.henselizationMap (IsLocalRing.maximalIdeal D.henselization) ∧
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      D.mapFromHenselization
        (IsLocalRing.maximalIdeal D.strictHenselization) ∧
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      D.strictMap (IsLocalRing.maximalIdeal D.strictHenselization) := by
  sorry

theorem henselization_isNoetherian_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    IsNoetherianRing R ↔
      IsNoetherianRing D.henselization ∧
        IsNoetherianRing D.strictHenselization := by
  sorry

theorem henselization_completion_isNoetherian_complete
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    (IsLocalRing
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.henselization)) ∧
      IsNoetherianRing
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.henselization)) ∧
      IsAdicComplete
        (Ideal.map (algebraMap D.henselization
          (Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.henselization)))
          (IsLocalRing.maximalIdeal D.henselization))
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.henselization))) ∧
    (IsLocalRing
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.strictHenselization)) ∧
      IsNoetherianRing
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.strictHenselization)) ∧
      IsAdicComplete
        (Ideal.map (algebraMap D.strictHenselization
          (Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.strictHenselization)))
          (IsLocalRing.maximalIdeal D.strictHenselization))
      (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.strictHenselization))) := by
  sorry

theorem henselization_completion_equiv
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    ∃ e :
        Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal R) ≃+*
          Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.henselization),
      e.toRingHom.comp
          (algebraMap R
            (Formalization.Books.Algebra.Unit96.ringCompletion
              (IsLocalRing.maximalIdeal R))) =
        (algebraMap D.henselization
          (Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.henselization))).comp
          D.henselizationMap := by
  sorry

theorem henselization_completion_flat
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    RingHom.Flat
      (algebraMap D.henselization
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.henselization))) ∧
    RingHom.Flat
      (algebraMap D.strictHenselization
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal D.strictHenselization))) := by
  sorry

theorem completion_to_strict_henselization_completion_formally_smooth
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    letI : Algebra R D.strictHenselization := D.strictMap.toAlgebra
    letI : IsLocalHom (algebraMap R D.strictHenselization) := D.strictLocal
    Formalization.Books.MoreAlgebra.Unit37.FormallySmoothForIdeal
      (Formalization.Books.Algebra.Unit97.completedLocalMap
        R D.strictHenselization)
      (Ideal.map
        (algebraMap D.strictHenselization
          (Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.strictHenselization)))
        (IsLocalRing.maximalIdeal D.strictHenselization)) := by
  sorry

theorem completed_strict_henselization_tensor_equiv
    {R K K' : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsNoetherianRing R]
    [Field K']
    [Algebra
      (IsLocalRing.ResidueField
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal R))) K']
    (D : StrictHenselizationData R K)
    (Dc : StrictHenselizationData
      (Formalization.Books.Algebra.Unit96.ringCompletion
        (IsLocalRing.maximalIdeal R)) K') :
    let e :
        Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal R) ≃+*
          Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.henselization) :=
      Classical.choose (henselization_completion_equiv D)
    letI : Algebra D.henselization
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal R)) :=
      (e.symm.toRingHom.comp
        (algebraMap D.henselization
          (Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.henselization)))).toAlgebra
    letI : Algebra D.henselization D.strictHenselization :=
      D.mapFromHenselization.toAlgebra
    Nonempty (
        Dc.strictHenselization ≃+*
          Formalization.Books.Algebra.Unit96.ringCompletion
              (IsLocalRing.maximalIdeal D.henselization) ⊗[D.henselization]
            D.strictHenselization) := by
  sorry

theorem completed_strict_henselization_completion_equiv
    {R K K' : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    [IsNoetherianRing R]
    [Field K']
    [Algebra
      (IsLocalRing.ResidueField
        (Formalization.Books.Algebra.Unit96.ringCompletion
          (IsLocalRing.maximalIdeal R))) K']
    (D : StrictHenselizationData R K)
    (Dc : StrictHenselizationData
      (Formalization.Books.Algebra.Unit96.ringCompletion
        (IsLocalRing.maximalIdeal R)) K') :
    Nonempty (
        Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal Dc.strictHenselization) ≃+*
          Formalization.Books.Algebra.Unit96.ringCompletion
            (IsLocalRing.maximalIdeal D.strictHenselization)) := by
  sorry

theorem henselization_isReduced_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    IsReduced R ↔ IsReduced D.henselization ∧
      IsReduced D.strictHenselization := by
  sorry

theorem henselization_nilradical_map
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    Ideal.map D.henselizationMap (nilradical R) =
        nilradical D.henselization ∧
    Ideal.map D.strictMap (nilradical R) =
        nilradical D.strictHenselization := by
  sorry

theorem henselization_isNormalDomain_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    Formalization.Books.Algebra.Unit37.IsNormalDomain R ↔
      Formalization.Books.Algebra.Unit37.IsNormalDomain D.henselization ∧
        Formalization.Books.Algebra.Unit37.IsNormalDomain
          D.strictHenselization := by
  sorry

theorem henselization_ringKrullDim_eq
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) :
    ringKrullDim R = ringKrullDim D.henselization ∧
    ringKrullDim R = ringKrullDim D.strictHenselization := by
  sorry

theorem henselization_localDepth_eq
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    Formalization.Books.Algebra.Unit72.localDepth R R =
        Formalization.Books.Algebra.Unit72.localDepth
          D.henselization D.henselization ∧
    Formalization.Books.Algebra.Unit72.localDepth R R =
        Formalization.Books.Algebra.Unit72.localDepth
          D.strictHenselization D.strictHenselization := by
  sorry

theorem henselization_isCohenMacaulayLocalRing_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    @Formalization.Books.Algebra.Unit104.IsCohenMacaulayLocalRing
        R _ _ inferInstance ↔
      (∃ hH : IsNoetherianRing D.henselization,
        @Formalization.Books.Algebra.Unit104.IsCohenMacaulayLocalRing
          D.henselization _ _ hH) ∧
      (∃ hSH : IsNoetherianRing D.strictHenselization,
        @Formalization.Books.Algebra.Unit104.IsCohenMacaulayLocalRing
          D.strictHenselization _ _ hSH) := by
  sorry

theorem henselization_isRegularLocalRing_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      IsRegularLocalRing D.henselization ∧
        IsRegularLocalRing D.strictHenselization := by
  sorry

theorem henselization_isDiscreteValuationRing_iff
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R] :
    (∃ hdom : IsDomain R, @IsDiscreteValuationRing R _ hdom) ↔
      (∃ hdom : IsDomain D.henselization,
        @IsDiscreteValuationRing D.henselization _ hdom) ∧
        (∃ hdom : IsDomain D.strictHenselization,
          @IsDiscreteValuationRing D.strictHenselization _ hdom) := by
  sorry

theorem filtered_colimit_etale_noetherian_fiber
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : IsFilteredColimitOfEtale f)
    (hB : IsNoetherianRing B) (p : PrimeSpectrum A) :
    letI : Algebra A B := f.toAlgebra
    ∃ n : ℕ, ∃ q : Fin n → PrimeSpectrum B,
      ∃ hq : ∀ i, (q i).asIdeal.comap f = p.asIdeal,
        (∀ q', q'.asIdeal.comap f = p.asIdeal ↔ ∃ i, q' = q i) ∧
        (Nonempty (B ⊗[A] p.asIdeal.ResidueField ≃+*
              (∀ i, (q i).asIdeal.ResidueField))) ∧
        ∀ i, ResidueFieldExtensionIsSeparableAlgebraic f p (q i)
          (hq i) := by
  sorry

theorem henselization_fiber_decomposition
    {R K : Type u} [CommRing R] [IsLocalRing R]
    [Field K] [Algebra (IsLocalRing.ResidueField R) K]
    (D : StrictHenselizationData R K) [IsNoetherianRing R]
    (p : PrimeSpectrum R) :
    (letI : Algebra R D.henselization := D.henselizationMap.toAlgebra
     ∃ t : ℕ, ∃ q : Fin t → PrimeSpectrum D.henselization,
       ∃ hq : ∀ i, (q i).asIdeal.comap D.henselizationMap = p.asIdeal,
        (∀ q', (q').asIdeal.comap D.henselizationMap = p.asIdeal ↔
          ∃ i, q' = q i) ∧
        (Nonempty (D.henselization ⊗[R] p.asIdeal.ResidueField ≃+*
              (∀ i, (q i).asIdeal.ResidueField))) ∧
        ∀ i, ResidueFieldExtensionIsSeparableAlgebraic
          D.henselizationMap p (q i) (hq i)) ∧
    (letI : Algebra R D.strictHenselization := D.strictMap.toAlgebra
     ∃ s : ℕ, ∃ r : Fin s → PrimeSpectrum D.strictHenselization,
       ∃ hr : ∀ i, (r i).asIdeal.comap D.strictMap = p.asIdeal,
        (∀ r', (r').asIdeal.comap D.strictMap = p.asIdeal ↔
          ∃ i, r' = r i) ∧
        (Nonempty (D.strictHenselization ⊗[R] p.asIdeal.ResidueField ≃+*
              (∀ i, (r i).asIdeal.ResidueField))) ∧
        ∀ i, ResidueFieldExtensionIsSeparableAlgebraic
          D.strictMap p (r i) (hr i)) := by
  sorry

end
end Formalization.Books.MoreAlgebra.Unit45
