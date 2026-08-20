import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit114.DimensionFiniteTypeAlgebras
import Formalization.Books.Algebra.Unit115.NoetherNormalization
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.SetTheory.Cardinal.ENat

/-!
# Commutative Algebra, Chapter 116: Dimension of finite type algebras over fields, reprise

The source's Krull dimensions use Mathlib's `ringKrullDim`, local dimensions
of spectra use the topological `krullDimensionAt`, and transcendence degrees
use the cardinal-valued `Algebra.trdeg`.  The tensor-product fibre in the
last statement uses the canonical `Unit112.tensorLocalRingOfFibre` interface.
-/

namespace Formalization.Books.Algebra.Unit116

universe u v

noncomputable section

open Set
open scoped TensorProduct
open Formalization.Books.Topology.Unit10

/-! ## Dimension and transcendence degree -/

/- The field of fractions is supplied as a field carrying the canonical
   algebra and scalar-tower structures over the finite-type domain. -/
theorem dimension_prime_polynomial_ring
    {k S : Type u} {K : Type v}
    [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K]
    [Algebra k K] [IsScalarTower k S K] :
    ∃ r : ℕ, Algebra.trdeg k K = r ∧
      ringKrullDim S = r ∧
        ∀ m : MaximalSpectrum S,
          ringKrullDim (Localization.AtPrime m.asIdeal) = r := by
  classical
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k S)
  have hI : RingHom.ker φ ≠ ⊤ := by
    intro hI
    have hzero : φ (1 : MvPolynomial (Fin n) k) = 0 := by
      have hmem : (1 : MvPolynomial (Fin n) k) ∈ RingHom.ker φ := by
        rw [hI]
        trivial
      exact hmem
    simp at hzero
  obtain ⟨r, _, g, hg, hgf, hdim, _⟩ :=
    Formalization.Books.Algebra.Unit115.noether_normalization
      (RingHom.ker φ) hI
  let e : (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) ≃ₐ[k] S :=
    AlgEquiv.ofBijective (Ideal.kerLiftAlg φ) ⟨
      Ideal.kerLiftAlg_injective φ, by
        intro s
        obtain ⟨p, hp⟩ := hφ s
        refine ⟨Ideal.Quotient.mk (RingHom.ker φ) p, ?_⟩
        exact (Ideal.kerLiftAlg_mk φ p).trans hp
        ⟩
  have hdimS : ringKrullDim S = r := by
    calc
      ringKrullDim S = ringKrullDim
        (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
      _ = r := hdim
  have htrdegS : Algebra.trdeg k S = r := by
    have htrdegQ : Algebra.trdeg k
        (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) = r := by
      let : IsDomain (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        e.toRingEquiv.isDomain_iff.mpr inferInstance
      let : Algebra (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := g.toAlgebra
      let : IsScalarTower k (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
      have hfaith : FaithfulSMul (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
      let : FaithfulSMul (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := hfaith
      let : Module.Finite (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) := hgf
      let : Algebra.IsAlgebraic (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) :=
        Algebra.IsAlgebraic.of_finite _ _
      rw [← trdeg_add_eq k (MvPolynomial (Fin r) k)]
      have hz : Algebra.trdeg (MvPolynomial (Fin r) k)
          (MvPolynomial (Fin n) k ⧸ RingHom.ker φ) = 0 := trdeg_eq_zero
      rw [hz, add_zero]
      simp [MvPolynomial.trdeg_of_isDomain]
    simpa using e.trdeg_eq.symm.trans htrdegQ
  have htrdegK : Algebra.trdeg k K = r := by
    let : Algebra.IsAlgebraic S K := IsLocalization.isAlgebraic K (nonZeroDivisors S)
    have hfaith : FaithfulSMul S K :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective S K)
    let : FaithfulSMul S K := hfaith
    have h := lift_trdeg_add_eq k S K
    rw [htrdegS, trdeg_eq_zero] at h
    simpa using h.symm
  refine ⟨r, htrdegK, hdimS, ?_⟩
  intro m
  exact (Formalization.Books.Algebra.Unit114.dimension_spell_it_out
    (k := k) (S := S) m).symm.trans hdimS

/- The residue-field transcendence degree strictly decreases along a proper
   specialization. -/
theorem tr_deg_specialization
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (q q' : PrimeSpectrum S) (hqq' : q < q') :
    Algebra.trdeg k q'.asIdeal.ResidueField <
      Algebra.trdeg k q.asIdeal.ResidueField := by
  let A := S ⧸ q.asIdeal
  let A' := S ⧸ q'.asIdeal
  have hqdim := dimension_prime_polynomial_ring
    (k := k) (S := A) (K := q.asIdeal.ResidueField)
  have hq'dim := dimension_prime_polynomial_ring
    (k := k) (S := A') (K := q'.asIdeal.ResidueField)
  obtain ⟨r, htr, hdim, _⟩ := hqdim
  obtain ⟨r', htr', hdim', _⟩ := hq'dim
  have hqq'ideal : q.asIdeal ≤ q'.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal q q').mpr hqq'.le
  obtain ⟨x, hxq', hxq⟩ := SetLike.exists_of_lt
    ((PrimeSpectrum.asIdeal_lt_asIdeal q q').mpr hqq')
  have hxne : Ideal.Quotient.mk q.asIdeal x ≠ 0 := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hxq
  have hxreg : Ideal.Quotient.mk q.asIdeal x ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact hxne
  have hdimlt : ringKrullDim A' + 1 ≤ ringKrullDim A := by
    apply ringKrullDim_succ_le_of_surjective
      (Ideal.Quotient.factor hqq'ideal)
      (Ideal.Quotient.factor_surjective hqq'ideal)
      hxreg
    exact Ideal.Quotient.factor_mk hqq'ideal x ▸
      (Ideal.Quotient.eq_zero_iff_mem.mpr hxq')
  have hnat : r' + 1 ≤ r := by
    rw [hdim', hdim] at hdimlt
    exact_mod_cast hdimlt
  rw [htr', htr]
  exact_mod_cast (show r' < r by omega)

/- The local dimension formula at an arbitrary point of a finite-type affine
   algebra over a field. -/
theorem dimension_at_a_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : PrimeSpectrum S) :
    krullDimensionAt p =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        ((Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : ℕ∞) :
          WithBot ℕ∞) := by
  sorry

/- The codimension formula for a surjective finite-type map is written using
   the canonical comap point and the corresponding prime heights. -/
theorem codimension
    {k S' S : Type u} [Field k]
    [CommRing S'] [CommRing S] [Algebra k S'] [Algebra k S]
    [Algebra.FiniteType k S'] [Algebra.FiniteType k S]
    (f : S' →ₐ[k] S) (hf : Function.Surjective f)
    (p : PrimeSpectrum S) :
    WithBot.unbotD 0 (krullDimensionAt (PrimeSpectrum.comap f.toRingHom p)) -
        WithBot.unbotD 0 (krullDimensionAt p) =
      (PrimeSpectrum.comap f.toRingHom p).asIdeal.height - p.asIdeal.height := by
  sorry

/-! ## Base change by a field extension -/

private structure TensorDimensionWitness
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K] (r : ℕ) where
  dimension : ringKrullDim (K ⊗[k] S) = r

/- The global Krull dimension is unchanged by extension of the ground field. -/
theorem dimension_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K] :
    ringKrullDim S = ringKrullDim (K ⊗[k] S) := by
  classical
  by_cases hS : Nontrivial S
  · let _ : Nontrivial S := hS
    obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k S)
    have hI : RingHom.ker φ ≠ ⊤ := by
      intro hI
      have hzero : φ (1 : MvPolynomial (Fin n) k) = 0 := by
        have hmem : (1 : MvPolynomial (Fin n) k) ∈ RingHom.ker φ := by
          rw [hI]
          trivial
        exact hmem
      simp at hzero
    let A := (MvPolynomial (Fin n) k) ⧸ RingHom.ker φ
    let e : A ≃ₐ[k] S :=
      AlgEquiv.ofBijective (Ideal.kerLiftAlg φ) ⟨
        Ideal.kerLiftAlg_injective φ, by
          intro s
          obtain ⟨p, hp⟩ := hφ s
          refine ⟨Ideal.Quotient.mk (RingHom.ker φ) p, ?_⟩
          exact (Ideal.kerLiftAlg_mk φ p).trans hp
          ⟩
    obtain ⟨r, _, g, hginj, hgfinite, hdim, _⟩ :=
      Formalization.Books.Algebra.Unit115.noether_normalization
        (RingHom.ker φ) hI
    have hdimS : ringKrullDim S = r := by
      calc
        ringKrullDim S = ringKrullDim A :=
          (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm
        _ = r := hdim
    let eK : (K ⊗[k] A) ≃ₐ[K] (K ⊗[k] S) :=
      Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
    let pK : (K ⊗[k] MvPolynomial (Fin r) k) ≃ₐ[K]
        MvPolynomial (Fin r) K :=
      MvPolynomial.algebraTensorAlgEquiv k K
    let hdimKData : TensorDimensionWitness (k := k) (S := S) (K := K) r := by
      let cKP : CommRing (K ⊗[k] MvPolynomial (Fin r) k) := inferInstance
      let cKA : CommRing (K ⊗[k] A) := inferInstance
      let cPK : CommRing (MvPolynomial (Fin r) k ⊗[k] K) := inferInstance
      letI cAK : CommRing (A ⊗[k] K) := inferInstance
      let gT : (K ⊗[k] MvPolynomial (Fin r) k) →+*
          (K ⊗[k] A) :=
        (Algebra.TensorProduct.map (AlgHom.id K K) g).toRingHom
      let gK : MvPolynomial (Fin r) K →+* (K ⊗[k] S) :=
        eK.toRingEquiv.toRingHom.comp
          (gT.comp pK.symm.toRingEquiv.toRingHom)
      have hgTinj : Function.Injective gT := by
        change Function.Injective ((g.toLinearMap).lTensor K)
        exact Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hginj
      have hgKinj : Function.Injective gK := by
        exact eK.injective.comp (hgTinj.comp pK.symm.injective)
      have hgTfinite : RingHom.Finite gT := by
        let gT' : (MvPolynomial (Fin r) k ⊗[k] K) →+* (A ⊗[k] K) :=
          (Algebra.TensorProduct.map g (AlgHom.id k K)).toRingHom
        have hgT'finite : RingHom.Finite gT' :=
          RingHom.Finite.tensorProductMap hgfinite (AlgHom.Finite.id k K)
        have hcomm :
            (Algebra.TensorProduct.comm k A K).toRingEquiv.toRingHom.comp
                (gT'.comp (Algebra.TensorProduct.comm k K
                  (MvPolynomial (Fin r) k)).toRingEquiv.toRingHom) = gT := by
          ext <;> simp [gT, gT']
        rw [← hcomm]
        exact (Algebra.TensorProduct.comm k A K).toRingEquiv.finite.comp
          (hgT'finite.comp
            (Algebra.TensorProduct.comm k K (MvPolynomial (Fin r) k)).toRingEquiv.finite)
      have hgKfinite : RingHom.Finite gK := by
        exact eK.toRingEquiv.finite.comp
          (hgTfinite.comp pK.symm.toRingEquiv.finite)
      have hdimK : ringKrullDim (K ⊗[k] S) = r := by
        have hdim' : ringKrullDim (MvPolynomial (Fin r) K) =
          ringKrullDim (K ⊗[k] S) :=
          Formalization.Books.Algebra.Unit112.integral_subring_ringKrullDim_eq
            gK hgKinj hgKfinite.to_isIntegral
        calc
          ringKrullDim (K ⊗[k] S) = ringKrullDim (MvPolynomial (Fin r) K) := hdim'.symm
          _ = r := by
            rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
              ringKrullDim_eq_zero_of_field]
            simp
      exact ⟨hdimK⟩
    exact hdimS.trans hdimKData.dimension.symm
  · let _ : Subsingleton S := not_nontrivial_iff_subsingleton.mp hS
    have : Subsingleton (K ⊗[k] S) := inferInstance
    simp only [ringKrullDim_eq_bot_of_subsingleton]

/- The local dimension is unchanged at corresponding points after base change.
   The right tensor inclusion is the map defining “lying over” here. -/
theorem dimension_at_a_point_preserved_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    krullDimensionAt q = krullDimensionAt qK := by
  sorry

/- The local fibre dimension is both the difference of local Krull
   dimensions and the difference of the corresponding transcendence degrees;
   a prime minimal over the extended prime gives fibre dimension zero. -/
theorem inequalities_under_field_extension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK =
        q) :
    WithBot.unbotD 0
          (ringKrullDim
            (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
              q qK hlying)) =
        WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) ∧
      WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime qK.asIdeal)) -
          WithBot.unbotD 0 (ringKrullDim (Localization.AtPrime q.asIdeal)) =
        Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) -
          Cardinal.toENat (Algebra.trdeg K qK.asIdeal.ResidueField) ∧
      ∃ qK' : PrimeSpectrum (K ⊗[k] S),
        ∃ hlying' : PrimeSpectrum.comap
              (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom qK' =
            q,
          WithBot.unbotD 0
              (ringKrullDim
                (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre
                  (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
                  q qK' hlying')) = 0 := by
  sorry

end

end Formalization.Books.Algebra.Unit116
