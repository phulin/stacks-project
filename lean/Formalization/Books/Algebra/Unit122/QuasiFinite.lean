import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit17.Spectrum
import Formalization.Books.Topology.Unit26.Miscellany
import Formalization.Books.Algebra.Unit30.MoreOnImages
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit116.DimensionFiniteTypeAlgebrasReprise
import Formalization.Books.Algebra.Unit21.OpenAndClosed
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.ZariskisMainTheorem
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Commutative Algebra, Chapter 122: Quasi-finite maps

The fibre of a ring map at a prime is represented by Mathlib's canonical
`Ideal.Fiber` construction.  The point of that fibre corresponding to a prime
of the target is the earlier `tensorFibrePrime` interface, and its local ring
is `tensorLocalRingOfFibre`.  The quasi-finite statements below use those
canonical constructions and Mathlib's `RingHom.QuasiFinite`,
`RingHom.QuasiFiniteAt`, `RingHom.FiniteType`, and `Module.Finite` interfaces.
-/

namespace Formalization.Books.Algebra.Unit122

open Set
open Formalization.Books.Topology.Unit26
open scoped TensorProduct

universe u v

noncomputable section

/-! ## Isolated points and fibres -/

/- The decomposition and localization assertions at the end of the source
   lemma are included with the six equivalent conditions rather than hidden
   in a proof-only interface. -/
theorem isolated_point_criteria
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : PrimeSpectrum S) :
    List.TFAE
        [ IsolatedPoint q,
          Module.Finite k (Localization.AtPrime q.asIdeal),
          ∃ g : S, g ∉ q.asIdeal ∧
            (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = {q},
          Formalization.Books.Topology.Unit10.krullDimensionAt q = 0,
          IsClosed ({q} : Set (PrimeSpectrum S)) ∧
            ringKrullDim (Localization.AtPrime q.asIdeal) = 0,
          Module.Finite k q.asIdeal.ResidueField ∧
            ringKrullDim (Localization.AtPrime q.asIdeal) = 0 ] ∧
      (∀ _hq : IsolatedPoint q,
        ∃ (S' : Type u) (hS' : CommRing S') (hA' : Algebra k S'),
          letI : CommRing S' := hS'
          letI : Algebra k S' := hA'
          Nonempty
              (S ≃+* (Localization.AtPrime q.asIdeal × S')) ∧
            Algebra.FiniteType k S' ∧
              ∀ g : S, g ∉ q.asIdeal →
                (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) = {q} →
                  Nonempty
                    (Localization.AtPrime q.asIdeal ≃+*
                      Localization.Away g)) := by
  classical
  have hne : (0 : S) ≠ 1 := by
    intro h
    apply q.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    rw [← h]
    exact q.asIdeal.zero_mem
  let : Nontrivial S := ⟨⟨0, 1, hne⟩⟩
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  constructor
  · tfae_have 1 ↔ 2 := by
      constructor
      · intro hq
        have : Algebra.QuasiFiniteAt k q.asIdeal :=
          Algebra.QuasiFiniteAt.of_isOpen_singleton (R := k) q hq
        exact (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
          (S := Localization.AtPrime q.asIdeal)).mp inferInstance
      · intro hq
        have : Algebra.QuasiFiniteAt k q.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
            (S := Localization.AtPrime q.asIdeal)).mpr hq
        change IsOpen ({q} : Set (PrimeSpectrum S))
        exact (Algebra.QuasiFiniteAt.isClopen_singleton (R := k) q).isOpen
    tfae_have 2 ↔ 3 := by
      constructor
      · intro hq
        have : Algebra.QuasiFiniteAt k q.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
            (S := Localization.AtPrime q.asIdeal)).mpr hq
        obtain ⟨g, hg, hq'⟩ :=
          Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton (R := k) q.asIdeal
        exact ⟨g, hg, by simpa using hq'⟩
      · rintro ⟨g, hg, hq⟩
        have : Algebra.QuasiFiniteAt k q.asIdeal :=
          Algebra.QuasiFiniteAt.of_isOpen_singleton (R := k) q
            (by rw [← hq]; exact PrimeSpectrum.isOpen_basicOpen)
        exact (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
          (S := Localization.AtPrime q.asIdeal)).mp inferInstance
    tfae_have 1 ↔ 5 := by
      constructor
      · intro hq
        have hclosed : IsClosed ({q} : Set (PrimeSpectrum S)) := by
          have h := ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
            0 2).mp hq
          exact h.1
        have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
          have : Algebra.QuasiFiniteAt k q.asIdeal :=
            Algebra.QuasiFiniteAt.of_isOpen_singleton (R := k) q hq
          have : Module.Finite k (Localization.AtPrime q.asIdeal) :=
            (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
              (S := Localization.AtPrime q.asIdeal)).mp inferInstance
          let : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
            IsArtinianRing.of_finite k (Localization.AtPrime q.asIdeal)
          exact Formalization.Books.Algebra.Unit60.noetherian_ringKrullDim_eq_zero_iff_artinian.mpr
            inferInstance
        exact ⟨hclosed, hdim⟩
      · rintro ⟨hclosed, hdim⟩
        have hheight : q.asIdeal.height = 0 := by
          apply WithBot.coe_eq_zero.mp
          calc
            (q.asIdeal.height : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q.asIdeal) :=
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
            _ = 0 := hdim
        have hmin : q.asIdeal ∈ minimalPrimes S :=
          Ideal.height_eq_zero_iff.mp hheight
        exact ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
          2 0 rfl rfl).mp ⟨hclosed,
            PrimeSpectrum.stableUnderGeneralization_singleton.mpr hmin⟩
    tfae_have 1 ↔ 6 := by
      constructor
      · intro hq
        have hclosed : IsClosed ({q} : Set (PrimeSpectrum S)) := by
          have h := ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
            0 2).mp hq
          exact h.1
        have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
          have : Algebra.QuasiFiniteAt k q.asIdeal :=
            Algebra.QuasiFiniteAt.of_isOpen_singleton (R := k) q hq
          have : Module.Finite k (Localization.AtPrime q.asIdeal) :=
            (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
              (S := Localization.AtPrime q.asIdeal)).mp inferInstance
          let : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
            IsArtinianRing.of_finite k (Localization.AtPrime q.asIdeal)
          exact Formalization.Books.Algebra.Unit60.noetherian_ringKrullDim_eq_zero_iff_artinian.mpr
            inferInstance
        let : Algebra.QuasiFiniteAt k q.asIdeal :=
          Algebra.QuasiFiniteAt.of_isOpen_singleton (R := k) q hq
        let : Module.Finite k (Localization.AtPrime q.asIdeal) :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing (R := k)
            (S := Localization.AtPrime q.asIdeal)).mp inferInstance
        have : Module.Finite k q.asIdeal.ResidueField := by
          exact Module.Finite.of_surjective
            (IsScalarTower.toAlgHom k (Localization.AtPrime q.asIdeal)
              q.asIdeal.ResidueField).toLinearMap
            (by simpa [IsLocalRing.ResidueField.algebraMap_eq] using
              (IsLocalRing.residue_surjective (R := Localization.AtPrime q.asIdeal)))
        exact ⟨inferInstance, hdim⟩
      · rintro ⟨hfinite, hdim⟩
        have : Module.Finite k q.asIdeal.ResidueField := hfinite
        have halg : Algebra.IsAlgebraic k q.asIdeal.ResidueField := inferInstance
        have hmax : q.asIdeal.IsMaximal := by
          have hcomap : (⊥ : Ideal k) = q.asIdeal.comap (algebraMap k S) := by
            have hnot : q.asIdeal.comap (algebraMap k S) ≠ ⊤ := by
              intro htop
              apply q.isPrime.ne_top
              rw [Ideal.eq_top_iff_one]
              have hone : (1 : k) ∈ q.asIdeal.comap (algebraMap k S) := by
                rw [htop]
                simp
              simpa using hone
            symm
            exact (Ideal.eq_bot_or_top _).resolve_right hnot
          exact Formalization.Books.Algebra.Unit35.maximal_residueField_isMaximal_of_algebraic
            (algebraMap k S) ⟨⊥, Ideal.bot_isMaximal⟩ q hcomap (by
              let : Algebra (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField :=
                Formalization.Books.Algebra.Unit35.residueFieldAlgebraOfMap
                  (⊥ : Ideal k) q.asIdeal (algebraMap k S) hcomap
              let : IsScalarTower k (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField := by
                constructor
                intro r x y
                obtain ⟨x, rfl⟩ :=
                  (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).surjective x
                have hmap (a : k) :
                    algebraMap (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField
                        (algebraMap k (⊥ : Ideal k).ResidueField a) =
                      algebraMap k q.asIdeal.ResidueField a := by
                  change Ideal.ResidueField.map (⊥ : Ideal k) q.asIdeal
                    (algebraMap k S) hcomap (algebraMap k (⊥ : Ideal k).ResidueField a) = _
                  exact Ideal.ResidueField.map_algebraMap
                    (⊥ : Ideal k) q.asIdeal (algebraMap k S) hcomap a
                simp only [Algebra.smul_def]
                rw [map_mul, hmap r]
                ring
              let : Algebra.IsAlgebraic k q.asIdeal.ResidueField := halg
              exact Algebra.IsAlgebraic.extendScalars
                (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).injective)
        have hclosed : IsClosed ({q} : Set (PrimeSpectrum S)) :=
          (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hmax
        have hheight : q.asIdeal.height = 0 := by
          apply WithBot.coe_eq_zero.mp
          calc
            (q.asIdeal.height : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q.asIdeal) :=
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
            _ = 0 := hdim
        have hmin : q.asIdeal ∈ minimalPrimes S :=
          Ideal.height_eq_zero_iff.mp hheight
        exact ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
          2 0 rfl rfl).mp ⟨hclosed,
            PrimeSpectrum.stableUnderGeneralization_singleton.mpr hmin⟩
    tfae_have 1 ↔ 4 := by
      constructor
      · intro hq
        apply le_antisymm
        · exact (Formalization.Books.Topology.Unit10.krullDimensionAt_le q hq
            (by simp)).trans (topologicalKrullDim_zero_of_discreteTopology _)
        · unfold Formalization.Books.Topology.Unit10.krullDimensionAt
          exact le_iInf fun U => by
            let x : U := ⟨q, U.mem⟩
            let : Nonempty (TopologicalSpace.IrreducibleCloseds (U : Set _)) :=
              let s : Set U := closure ({x} : Set U)
              ⟨⟨s, by
                exact (isIrreducible_singleton : IsIrreducible ({x} : Set U)).closure,
                isClosed_closure⟩⟩
            exact Order.krullDim_nonneg
      · intro hq
        have hformula :=
          Formalization.Books.Algebra.Unit116.dimension_at_a_point_finite_type_field
            (k := k) (S := S) q
        rw [hq] at hformula
        have hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0 := by
          have hcast_nonneg : 0 ≤
              ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                WithBot ℕ∞) := (WithBot.coe_nonneg).2 bot_le
          have hdim_nonneg : 0 ≤ ringKrullDim (Localization.AtPrime q.asIdeal) := by
            let : Nonempty (PrimeSpectrum (Localization.AtPrime q.asIdeal)) :=
              ⟨IsLocalRing.closedPoint _⟩
            exact Order.krullDim_nonneg
          apply le_antisymm
          · calc
              ringKrullDim (Localization.AtPrime q.asIdeal) ≤
                  ringKrullDim (Localization.AtPrime q.asIdeal) +
                    ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                      WithBot ℕ∞) := by
                        simpa using add_le_add_right hcast_nonneg _
              _ = 0 := hformula.symm
          · exact hdim_nonneg
        have htrdeg : Algebra.trdeg k q.asIdeal.ResidueField = 0 := by
          have hcast :
              ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                WithBot ℕ∞) = 0 := by
            have hdim_nonneg : 0 ≤ ringKrullDim (Localization.AtPrime q.asIdeal) := by
              let : Nonempty (PrimeSpectrum (Localization.AtPrime q.asIdeal)) :=
                ⟨IsLocalRing.closedPoint _⟩
              exact Order.krullDim_nonneg
            apply le_antisymm
            · calc
                ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                    WithBot ℕ∞) ≤
                    ringKrullDim (Localization.AtPrime q.asIdeal) +
                      ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                        WithBot ℕ∞) := by
                          simpa [add_comm] using add_le_add_left hdim_nonneg
                            ((Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) : ℕ∞) :
                              WithBot ℕ∞)
                _ = 0 := hformula.symm
            · exact (WithBot.coe_nonneg).2 bot_le
          exact Cardinal.toENat_eq_zero.mp (WithBot.coe_eq_zero.mp hcast)
        have : Algebra.IsAlgebraic k q.asIdeal.ResidueField :=
          (trdeg_eq_zero_iff.mp htrdeg)
        have hmax : q.asIdeal.IsMaximal := by
          have hcomap : (⊥ : Ideal k) = q.asIdeal.comap (algebraMap k S) := by
            have hnot : q.asIdeal.comap (algebraMap k S) ≠ ⊤ := by
              intro htop
              apply q.isPrime.ne_top
              rw [Ideal.eq_top_iff_one]
              have hone : (1 : k) ∈ q.asIdeal.comap (algebraMap k S) := by
                rw [htop]
                simp
              simpa using hone
            symm
            exact (Ideal.eq_bot_or_top _).resolve_right hnot
          exact Formalization.Books.Algebra.Unit35.maximal_residueField_isMaximal_of_algebraic
            (algebraMap k S) ⟨⊥, Ideal.bot_isMaximal⟩ q hcomap (by
              let : Algebra (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField :=
                Formalization.Books.Algebra.Unit35.residueFieldAlgebraOfMap
                  (⊥ : Ideal k) q.asIdeal (algebraMap k S) hcomap
              let : IsScalarTower k (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField := by
                constructor
                intro r x y
                obtain ⟨x, rfl⟩ :=
                  (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).surjective x
                have hmap (a : k) :
                    algebraMap (⊥ : Ideal k).ResidueField q.asIdeal.ResidueField
                        (algebraMap k (⊥ : Ideal k).ResidueField a) =
                      algebraMap k q.asIdeal.ResidueField a := by
                  change Ideal.ResidueField.map (⊥ : Ideal k) q.asIdeal
                    (algebraMap k S) hcomap (algebraMap k (⊥ : Ideal k).ResidueField a) = _
                  exact Ideal.ResidueField.map_algebraMap
                    (⊥ : Ideal k) q.asIdeal (algebraMap k S) hcomap a
                simp only [Algebra.smul_def]
                rw [map_mul, hmap r]
                ring
              let : Algebra.IsAlgebraic k q.asIdeal.ResidueField := inferInstance
              exact Algebra.IsAlgebraic.extendScalars
                (Ideal.algEquivResidueFieldOfField (⊥ : Ideal k)).injective)
        have hclosed : IsClosed ({q} : Set (PrimeSpectrum S)) :=
          (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hmax
        have hheight : q.asIdeal.height = 0 := by
          apply WithBot.coe_eq_zero.mp
          calc
            (q.asIdeal.height : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime q.asIdeal) :=
              (IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
                (Localization.AtPrime q.asIdeal)).symm
            _ = 0 := hdim
        have hmin : q.asIdeal ∈ minimalPrimes S :=
          Ideal.height_eq_zero_iff.mp hheight
        exact ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
          2 0 rfl rfl).mp ⟨hclosed,
            PrimeSpectrum.stableUnderGeneralization_singleton.mpr hmin⟩
    tfae_finish
  · intro hq
    have hclosed : IsClosed ({q} : Set (PrimeSpectrum S)) := by
      have h := ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing q).out
        0 2).mp hq
      exact h.1
    obtain ⟨e, ⟨he, heq⟩, -⟩ :=
      Formalization.Books.Algebra.Unit21.existsUnique_idempotent_basicOpen_eq_of_isClopen
        ⟨hclosed, hq⟩
    have haway : IsLocalization.Away e (Localization.AtPrime q.asIdeal) :=
      (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
        (p := q) (S := Localization.AtPrime q.asIdeal) heq.symm).mpr inferInstance
    let : IsLocalization.Away e (Localization.AtPrime q.asIdeal) := haway
    refine ⟨Localization.Away (1 - e), inferInstance, inferInstance, ?_, ?_, ?_⟩
    · let eLoc : Localization.Away e ≃+* Localization.AtPrime q.asIdeal :=
        (IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e)
          (Localization.AtPrime q.asIdeal)).toRingEquiv
      let : IsLocalization.Away e
          (S ⧸ Ideal.span ({1 - e} : Set S)) :=
        IsLocalization.Away.quotient_of_isIdempotentElem he
      let : IsLocalization.Away (1 - e)
          (S ⧸ Ideal.span ({e} : Set S)) := by
        have h := IsLocalization.Away.quotient_of_isIdempotentElem he.one_sub
        rw [sub_sub_cancel] at h
        exact h
      let awayE : Localization.Away e ≃+*
          S ⧸ Ideal.span ({1 - e} : Set S) :=
        (IsLocalization.algEquiv (Submonoid.powers e) (Localization.Away e)
          (S ⧸ Ideal.span ({1 - e} : Set S))).toRingEquiv
      let awayOneSub : Localization.Away (1 - e) ≃+*
          S ⧸ Ideal.span ({e} : Set S) :=
        (IsLocalization.algEquiv (Submonoid.powers (1 - e))
          (Localization.Away (1 - e))
          (S ⧸ Ideal.span ({e} : Set S))).toRingEquiv
      let qprod : S ≃+*
          (S ⧸ Ideal.span ({1 - e} : Set S)) ×
            (S ⧸ Ideal.span ({e} : Set S)) :=
        (AlgEquiv.prodQuotientOfIsIdempotentElem S he.one_sub he
          (by ring) (by simpa using he.one_sub_mul_self)).toRingEquiv
      exact ⟨qprod.trans
        ((RingEquiv.prodCongr awayE.symm awayOneSub.symm).trans
          (RingEquiv.prodCongr eLoc (RingEquiv.refl _)))⟩
    · infer_instance
    · intro g hg hgb
      have hawayg : IsLocalization.Away g (Localization.AtPrime q.asIdeal) :=
        (PrimeSpectrum.isLocalization_away_iff_atPrime_of_basicOpen_eq_singleton
          (p := q) (S := Localization.AtPrime q.asIdeal) hgb).mpr inferInstance
      let : IsLocalization.Away g (Localization.AtPrime q.asIdeal) := hawayg
      exact ⟨(IsLocalization.algEquiv (Submonoid.powers g)
        (Localization.AtPrime q.asIdeal) (Localization.Away g)).toRingEquiv⟩

/- The map from `R_f` to `S_{f g}` is the canonical localization map from
   Chapter 30.  The target prime is the unique extension of `q` to the
   standard open, written using the Chapter 17 homeomorphism. -/
noncomputable def localizedPrimeAwayMul
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p) (a : R) (b : S)
    (ha : a ∉ p.asIdeal) (hb : b ∉ q.asIdeal) :
    PrimeSpectrum (Localization.Away (f a * b)) := by
  have hfa : f a ∉ q.asIdeal := by
    intro hfa
    apply ha
    have hmem : a ∈ (PrimeSpectrum.comap f q).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using hfa
    simpa [hq] using hmem
  have hprod : f a * b ∉ q.asIdeal := by
    intro hprod
    rcases q.isPrime.mem_or_mem hprod with hfa' | hb'
    · exact hfa hfa'
    · exact hb hb'
  exact Formalization.Books.Algebra.Unit17.standardOpenSpectrumInverse
    (f a * b) ⟨q, (PrimeSpectrum.mem_basicOpen (f a * b) q).mpr hprod⟩

theorem isolated_point_fibre_criteria
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
    List.TFAE
      [ IsolatedPoint
          (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq),
        Module.Finite p.asIdeal.ResidueField
          (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq),
        ∃ g : S, g ∉ q.asIdeal ∧
          ∀ q' : PrimeSpectrum S,
            q' ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) →
              PrimeSpectrum.comap f q' = p → q' = q,
        Formalization.Books.Topology.Unit10.krullDimensionAt
            (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq) = 0,
        IsClosed
            ({Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq} :
              Set (PrimeSpectrum (p.asIdeal.Fiber S))) ∧
          ringKrullDim
              (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq) = 0,
        Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField ∧
          ringKrullDim
              (Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq) = 0 ] := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt f p q hq).toAlgebra
  let : Algebra.FiniteType R S := hfinite
  let : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    by infer_instance
  let qF := Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq
  let T := Formalization.Books.Algebra.Unit112.tensorLocalRingOfFibre f p q hq
  have hqF : qF.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
    have hleft :=
      (PrimeSpectrum.preimageEquivFiber R S p).left_inv
        (⟨q, by simpa [RingHom.algebraMap_toAlgebra] using hq⟩ :
          PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
    have hleft' := congrArg
      (fun z : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} => z.1.asIdeal) hleft
    exact hleft'
  let : q.asIdeal.LiesOver p.asIdeal := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def]
    simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
      (congrArg PrimeSpectrum.asIdeal hq).symm
  have hqF_of_hq : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal →
      RingHom.QuasiFiniteAt f q.asIdeal := by
    intro hqFq
    let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal := hqFq
    exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField p.asIdeal q.asIdeal
      qF.asIdeal hqF
  have hq_of_hqF : RingHom.QuasiFiniteAt f q.asIdeal →
      Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal := by
    intro hqf
    let : Algebra.QuasiFiniteAt R q.asIdeal := hqf
    exact Algebra.QuasiFiniteAt.baseChange q.asIdeal qF.asIdeal hqF.symm
  have hcrit := isolated_point_criteria
    (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) qF
  tfae_have 1 ↔ 2 := by
      simpa [qF, T] using hcrit.1.out 0 1
  tfae_have 2 ↔ 4 := by
      simpa [qF, T] using hcrit.1.out 1 3
  tfae_have 2 ↔ 5 := by
      simpa [qF, T] using hcrit.1.out 1 4
  tfae_have 1 ↔ 3 := by
      constructor
      · intro hqiso
        have hlocal : Module.Finite p.asIdeal.ResidueField
            (Localization.AtPrime qF.asIdeal) :=
          (hcrit.1.out 0 1).mp hqiso
        let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p.asIdeal.ResidueField) (S := Localization.AtPrime qF.asIdeal)).mpr
            hlocal
        have hqR : RingHom.QuasiFiniteAt f q.asIdeal := hqF_of_hq inferInstance
        let : Algebra.QuasiFiniteAt R q.asIdeal := hqR
        obtain ⟨g, hg, hmem⟩ :=
          Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
            p.asIdeal q.asIdeal
        refine ⟨g, hg, ?_⟩
        intro q' hq' hcomap
        by_contra hne
        have hne' : q'.asIdeal ≠ q.asIdeal := by
          intro heq
          apply hne
          exact PrimeSpectrum.ext heq
        have hlie : q'.asIdeal.LiesOver p.asIdeal := by
          rw [Ideal.liesOver_iff, Ideal.under_def]
          simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
            (congrArg PrimeSpectrum.asIdeal hcomap).symm
        exact (PrimeSpectrum.mem_basicOpen g q').mp hq'
          (hmem q'.asIdeal q'.isPrime hne' hlie)
      · rintro ⟨g, hg, huniq⟩
        have hopen : IsOpen (X :=
            PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
            {⟨q, by simpa [RingHom.algebraMap_toAlgebra] using hq⟩} := by
          have hopen' := PrimeSpectrum.isOpen_basicOpen (a := g)
          have hpre :
              (fun x : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} => x.1) ⁻¹'
                  (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) =
                {⟨q, by simpa [RingHom.algebraMap_toAlgebra] using hq⟩} := by
            ext x
            constructor
            · intro hx
              apply Subtype.ext
              apply huniq x.1
              · simpa using hx
              · have hxcomap : PrimeSpectrum.comap (algebraMap R S) x.1 = p := x.2
                simpa [RingHom.algebraMap_toAlgebra] using hxcomap
            · rintro rfl
              exact (PrimeSpectrum.mem_basicOpen g q).mpr hg
          rw [← hpre]
          exact hopen'.preimage continuous_subtype_val
        have hqf : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal := by
          have hqR : Algebra.QuasiFiniteAt R q.asIdeal := by
            cases hq
            exact Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber q hopen
          let : Algebra.QuasiFiniteAt R q.asIdeal := hqR
          exact Algebra.QuasiFiniteAt.baseChange q.asIdeal qF.asIdeal hqF.symm
        let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal := hqf
        exact (hcrit.1.out 0 1).mpr
          ((Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p.asIdeal.ResidueField) (S := T)).mp inferInstance)
  tfae_have 1 ↔ 6 := by
      constructor
      · intro hqiso
        have hlocal : Module.Finite p.asIdeal.ResidueField T :=
          tfae_1_iff_2.mp hqiso
        have : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p.asIdeal.ResidueField) (S := T)).mpr hlocal
        have hqR : RingHom.QuasiFiniteAt f q.asIdeal := hqF_of_hq inferInstance
        let : Algebra.QuasiFiniteAt R q.asIdeal := hqR
        have hbase : p.asIdeal = q.asIdeal.comap (algebraMap R S) := by
          simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
            (congrArg PrimeSpectrum.asIdeal hq).symm
        let : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
          IsScalarTower.of_algebraMap_eq' (by
            ext r
            change algebraMap S q.asIdeal.ResidueField (algebraMap R S r) =
              Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hbase
                (algebraMap R p.asIdeal.ResidueField r)
            exact (Ideal.ResidueField.map_algebraMap
              p.asIdeal q.asIdeal (algebraMap R S) hbase r).symm)
        have : Module.Finite p.asIdeal.ResidueField T := hlocal
        have hfinite_residue : Module.Finite p.asIdeal.ResidueField
            q.asIdeal.ResidueField := by
          let : Algebra (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime q.asIdeal) :=
            Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
          let : Localization.AtPrime.IsLiesOverAlgebra p.asIdeal q.asIdeal :=
            ⟨rfl⟩
          convert Algebra.WeaklyQuasiFiniteAt.finite_residueField
            p.asIdeal q.asIdeal using 1
          apply Module.ext'
          intro r x
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
          let canonicalAlg : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
            Ideal.Quotient.algebraOfLiesOver
              (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          let : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := canonicalAlg
          obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
          change IsLocalRing.residue (Localization.AtPrime q.asIdeal)
              ((algebraMap (Localization.AtPrime p.asIdeal)
                (Localization.AtPrime q.asIdeal)) r * x) =
            IsLocalRing.residue (Localization.AtPrime q.asIdeal)
              ((algebraMap (Localization.AtPrime p.asIdeal)
                (Localization.AtPrime q.asIdeal)) r) *
              IsLocalRing.residue (Localization.AtPrime q.asIdeal) x
          rw [map_mul]
        exact ⟨hfinite_residue, (tfae_2_iff_5.mp hlocal).2⟩
      · rintro ⟨hfiniteq, hdim⟩
        have hbase : p.asIdeal = q.asIdeal.comap (algebraMap R S) := by
          simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
            (congrArg PrimeSpectrum.asIdeal hq).symm
        let : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
          IsScalarTower.of_algebraMap_eq' (by
            ext r
            change algebraMap S q.asIdeal.ResidueField (algebraMap R S r) =
              Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) hbase
                (algebraMap R p.asIdeal.ResidueField r)
            exact (Ideal.ResidueField.map_algebraMap
              p.asIdeal q.asIdeal (algebraMap R S) hbase r).symm)
        let φ : p.asIdeal.Fiber S →ₐ[p.asIdeal.ResidueField]
            q.asIdeal.ResidueField := Algebra.TensorProduct.lift
          (Algebra.ofId _ _) (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField)
            (fun _ _ ↦ .all _ _)
        let φR : p.asIdeal.Fiber S →ₐ[R] q.asIdeal.ResidueField := Algebra.TensorProduct.lift
          (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R S) hbase)
          (IsScalarTower.toAlgHom R S q.asIdeal.ResidueField) (fun _ _ ↦ .all _ _)
        have hφ : φ.toRingHom = φR.toRingHom := by
          ext <;> simp [φ, φR]
        have hkerR : qF.asIdeal = RingHom.ker φR.toRingHom := by
          change (PrimeSpectrum.preimageEquivFiber R S p
            (⟨q, by simpa [RingHom.algebraMap_toAlgebra] using hq⟩ :
              PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})).asIdeal = _
          rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]
        have hker : qF.asIdeal = RingHom.ker φ.toRingHom := by
          rw [hφ]
          exact hkerR
        let : Algebra p.asIdeal.ResidueField qF.asIdeal.ResidueField :=
          IsLocalRing.ResidueField.algebra (Localization.AtPrime qF.asIdeal)
        let ψ : qF.asIdeal.ResidueField →ₐ[p.asIdeal.ResidueField]
            q.asIdeal.ResidueField :=
          Ideal.ResidueField.liftₐ qF.asIdeal φ (by
            rw [hker]
            exact le_rfl) (by
            intro x hx
            have hx0 : φ x ≠ 0 := by
              intro hzero
              apply hx
              rw [hker]
              exact hzero
            exact isUnit_iff_ne_zero.mpr hx0)
        have hψ : Function.Injective ψ := by
          exact RingHom.injective ψ.toRingHom
        let : Module.Finite p.asIdeal.ResidueField q.asIdeal.ResidueField := hfiniteq
        let : Algebra.IsAlgebraic p.asIdeal.ResidueField q.asIdeal.ResidueField :=
          Algebra.IsAlgebraic.of_finite _ _
        let : Algebra.IsAlgebraic p.asIdeal.ResidueField qF.asIdeal.ResidueField :=
          Algebra.IsAlgebraic.of_injective ψ hψ
        have hcomap : (⊥ : Ideal p.asIdeal.ResidueField) =
            qF.asIdeal.comap (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
          have hnot : qF.asIdeal.comap
              (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) ≠ ⊤ := by
            intro htop
            apply qF.isPrime.ne_top
            rw [Ideal.eq_top_iff_one]
            have hone : (1 : p.asIdeal.ResidueField) ∈
                qF.asIdeal.comap
                  (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
              rw [htop]
              simp
            change algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)
                (1 : p.asIdeal.ResidueField) ∈ qF.asIdeal at hone
            simpa only [map_one] using hone
          symm
          exact (Ideal.eq_bot_or_top _).resolve_right hnot
        have hmax : qF.asIdeal.IsMaximal := by
          exact Formalization.Books.Algebra.Unit35.maximal_residueField_isMaximal_of_algebraic
            (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
            ⟨⊥, Ideal.bot_isMaximal⟩ qF hcomap (by
              let : Algebra (⊥ : Ideal p.asIdeal.ResidueField).ResidueField
                  qF.asIdeal.ResidueField :=
                Formalization.Books.Algebra.Unit35.residueFieldAlgebraOfMap
                  (⊥ : Ideal p.asIdeal.ResidueField) qF.asIdeal
                  (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) hcomap
              let : IsScalarTower p.asIdeal.ResidueField
                  (⊥ : Ideal p.asIdeal.ResidueField).ResidueField
                  qF.asIdeal.ResidueField := by
                constructor
                intro r x y
                obtain ⟨x, rfl⟩ :=
                  (Ideal.algEquivResidueFieldOfField
                    (⊥ : Ideal p.asIdeal.ResidueField)).surjective x
                have hmap (a : p.asIdeal.ResidueField) :
                    algebraMap (⊥ : Ideal p.asIdeal.ResidueField).ResidueField
                        qF.asIdeal.ResidueField
                        (algebraMap p.asIdeal.ResidueField
                          (⊥ : Ideal p.asIdeal.ResidueField).ResidueField a) =
                      algebraMap p.asIdeal.ResidueField qF.asIdeal.ResidueField a := by
                  change Ideal.ResidueField.map (⊥ : Ideal p.asIdeal.ResidueField)
                      qF.asIdeal (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S))
                      hcomap
                      (algebraMap p.asIdeal.ResidueField
                        (⊥ : Ideal p.asIdeal.ResidueField).ResidueField a) = _
                  exact Ideal.ResidueField.map_algebraMap
                    (⊥ : Ideal p.asIdeal.ResidueField) qF.asIdeal
                    (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) hcomap a
                    |>.trans (by
                      rw [IsScalarTower.algebraMap_apply p.asIdeal.ResidueField
                        (p.asIdeal.Fiber S) qF.asIdeal.ResidueField])
                simp only [Algebra.smul_def]
                rw [map_mul, hmap r]
                ring
              exact Algebra.IsAlgebraic.extendScalars
                (Ideal.algEquivResidueFieldOfField
                  (⊥ : Ideal p.asIdeal.ResidueField)).injective)
        have hclosed : IsClosed ({qF} : Set (PrimeSpectrum (p.asIdeal.Fiber S))) :=
          (PrimeSpectrum.isClosed_singleton_iff_isMaximal qF).mpr hmax
        exact (hcrit.1.out 4 0 rfl rfl).mp ⟨hclosed, hdim⟩
  tfae_finish

/-! ## Quasi-finite maps -/

/- Mathlib's `RingHom.QuasiFinite` deliberately omits the finite-type
   hypothesis, whereas the source builds finite type into its definition.
   These source-facing wrappers retain that distinction while delegating the
   fibre condition to Mathlib's canonical interfaces. -/
def IsQuasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  RingHom.FiniteType f ∧ RingHom.QuasiFiniteAt f q.asIdeal

def IsQuasiFinite
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  RingHom.FiniteType f ∧ ∀ q : PrimeSpectrum S, RingHom.QuasiFiniteAt f q.asIdeal

theorem quasiFiniteAt_above_prime_criteria
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ ∀ q : PrimeSpectrum S,
          PrimeSpectrum.comap f q = p → IsQuasiFiniteAt f q,
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S),
        Finite (PrimeSpectrum (p.asIdeal.Fiber S)) ] := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Algebra.FiniteType R S := hfinite
  let : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    by infer_instance
  let p0 : PrimeSpectrum p.asIdeal.ResidueField := ⟨⊥, inferInstance⟩
  let : Subsingleton (PrimeSpectrum p.asIdeal.ResidueField) := by
    constructor
    intro x y
    apply PrimeSpectrum.ext
    have hx : x.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top x.asIdeal).resolve_right x.isPrime.ne_top
    have hy : y.asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top
    rw [hx, hy]
  have hmodule_of_finite_spec :
      Finite (PrimeSpectrum (p.asIdeal.Fiber S)) →
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    intro hspec
    let : Finite (PrimeSpectrum (p.asIdeal.Fiber S)) := hspec
    let : Algebra.QuasiFinite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      (Algebra.QuasiFinite.iff_finite_comap_preimage_singleton).mpr (by
        intro x
        have hx : x = p0 := Subsingleton.elim _ _
        rw [hx]
        have heq : PrimeSpectrum.comap
            (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) ⁻¹' {p0} =
            (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
          ext y
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
          exact Subsingleton.elim _ _
        rw [heq]
        exact Set.finite_univ)
    exact (Algebra.QuasiFinite.iff_of_isArtinianRing
      (R := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S)).mp inferInstance
  have hfinite_spec_of_module :
      Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) →
        Finite (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    intro hmodule
    let : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hmodule
    let : Algebra.QuasiFinite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      inferInstance
    have hpre := Algebra.QuasiFinite.finite_comap_preimage_singleton
      (R := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) p0
    have heq : PrimeSpectrum.comap
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) ⁻¹' {p0} =
        (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    apply Finite.of_finite_univ
    exact heq ▸ hpre
  have hfinite_spec_of_local :
      (∀ q : PrimeSpectrum S,
        PrimeSpectrum.comap f q = p → IsQuasiFiniteAt f q) →
        Finite (PrimeSpectrum (p.asIdeal.Fiber S)) := by
    intro hall
    let e := PrimeSpectrum.preimageHomeomorphFiber R S p
    have hdisc : IsDiscrete (Set.univ : Set (PrimeSpectrum (p.asIdeal.Fiber S))) := by
      apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
      intro x hx
      obtain ⟨z, rfl⟩ := e.surjective x
      have hz : PrimeSpectrum.comap f z.1 = p := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff,
          RingHom.algebraMap_toAlgebra] using z.2
      have hzq : RingHom.QuasiFiniteAt f z.1 := (hall z.1 hz).2
      have heq : (e z).asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom =
          z.1.asIdeal := by
        exact congr($(e.symm_apply_apply z).1.asIdeal)
      let : Algebra.QuasiFiniteAt R z.1.asIdeal := hzq
      let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField (e z).asIdeal :=
        Algebra.QuasiFiniteAt.baseChange z.1.asIdeal (e z).asIdeal heq.symm
      have hlocal : Module.Finite p.asIdeal.ResidueField
          (Localization.AtPrime (e z).asIdeal) :=
        (Algebra.QuasiFinite.iff_of_isArtinianRing
          (R := p.asIdeal.ResidueField)
          (S := Localization.AtPrime (e z).asIdeal)).mp inferInstance
      have hiso : IsolatedPoint (e z) :=
        (isolated_point_criteria
          (k := p.asIdeal.ResidueField) (S := p.asIdeal.Fiber S) (e z)).1.out
          0 1 |>.mpr hlocal
      exact ⟨{e z}, hiso, by simp⟩
    let : DiscreteTopology (PrimeSpectrum (p.asIdeal.Fiber S)) :=
      isDiscrete_univ_iff.mp hdisc
    let : CompactSpace (PrimeSpectrum (p.asIdeal.Fiber S)) :=
      PrimeSpectrum.compactSpace
    exact finite_of_compact_of_discrete
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hall
      exact hmodule_of_finite_spec (hfinite_spec_of_local hall)
    · intro hmodule q hq
      have : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hmodule
      let : Algebra.QuasiFinite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
        inferInstance
      have hqz : PrimeSpectrum.comap (algebraMap R S) q = p := by
        simpa [RingHom.algebraMap_toAlgebra] using hq
      have hqF :
          (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal.comap
              Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
        have hleft :=
          (PrimeSpectrum.preimageEquivFiber R S p).left_inv
            (⟨q, hqz⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
        have hleft' := congrArg
          (fun z : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} => z.1.asIdeal) hleft
        exact hleft'
      let : q.asIdeal.LiesOver p.asIdeal := by
        rw [Ideal.liesOver_iff, Ideal.under_def]
        simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
          (congrArg PrimeSpectrum.asIdeal hqz).symm
      let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField
          (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal := by
        let : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := hmodule
        let : IsArtinianRing (p.asIdeal.Fiber S) :=
          IsArtinianRing.of_finite p.asIdeal.ResidueField (p.asIdeal.Fiber S)
        have hloc_finite : Module.Finite (p.asIdeal.Fiber S)
          (Localization.AtPrime
            (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal) :=
          by
            apply Module.Finite.of_surjective (Algebra.linearMap _ _)
            exact IsArtinianRing.localization_surjective
              (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal.primeCompl
              _
        let : Module.Finite (p.asIdeal.Fiber S)
            (Localization.AtPrime
              (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal) :=
          hloc_finite
        have hlocal : Module.Finite p.asIdeal.ResidueField
            (Localization.AtPrime
              (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal) :=
          Module.Finite.trans (p.asIdeal.Fiber S)
            (Localization.AtPrime
              (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal)
        exact (Algebra.QuasiFinite.iff_of_isArtinianRing
          (R := p.asIdeal.ResidueField)
          (S := Localization.AtPrime
            (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal)).mpr
          hlocal
      have hq' : RingHom.QuasiFiniteAt f q.asIdeal := by
        exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField p.asIdeal q.asIdeal
          (Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hq).asIdeal hqF
      exact ⟨hfinite, hq'⟩
  tfae_have 2 ↔ 3 := by
    constructor
    · intro hmodule
      exact hfinite_spec_of_module hmodule
    · intro hspec
      exact hmodule_of_finite_spec hspec
  tfae_finish

theorem isQuasiFinite_iff_finite_fibres
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    IsQuasiFinite f ↔
      ∀ p : PrimeSpectrum R,
        Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  classical
  let : Algebra R S := f.toAlgebra
  constructor
  · rintro ⟨hft, hq⟩ p
    have hall : ∀ q : PrimeSpectrum S,
        PrimeSpectrum.comap f q = p → IsQuasiFiniteAt f q := by
      intro q hqp
      exact ⟨hft, hq q⟩
    exact (quasiFiniteAt_above_prime_criteria f p hft).out 0 1 |>.mp hall
  · intro hmodule
    refine ⟨hfinite, ?_⟩
    intro q
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q
    have hp : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      hmodule p
    have hall : ∀ q' : PrimeSpectrum S,
        PrimeSpectrum.comap f q' = p → IsQuasiFiniteAt f q' :=
      (quasiFiniteAt_above_prime_criteria f p hfinite).out 1 0 |>.mp hp
    exact (hall q rfl).2

theorem quasiFiniteAt_localization_iff
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap f q = p)
    (a : R) (ha : a ∉ p.asIdeal) (b : S) (hb : b ∉ q.asIdeal)
    (hfinite : RingHom.FiniteType f) :
    IsQuasiFiniteAt f q ↔
    IsQuasiFiniteAt
        (Formalization.Books.Algebra.Unit30.localizationAwayMulMap f a b)
        (localizedPrimeAwayMul f p q hq a b ha hb) := by
  classical
  let : Algebra R S := f.toAlgebra
  let α := Formalization.Books.Algebra.Unit30.localizationAwayMulMap f a b
  let T := Localization.Away (f a * b)
  let q' := localizedPrimeAwayMul f p q hq a b ha hb
  let : Algebra (Localization.Away a) T := α.toAlgebra
  have hbase : Algebra.QuasiFinite R (Localization (Submonoid.powers a)) := by
    exact Algebra.QuasiFinite.of_isLocalization
      (R := R) (S := R) (Submonoid.powers a)
  have hfa : f a ∉ q.asIdeal := by
    intro hfa
    apply ha
    have hmem : a ∈ (PrimeSpectrum.comap f q).asIdeal := by
      simpa [PrimeSpectrum.comap_asIdeal] using hfa
    simpa [hq] using hmem
  have hpow : ∀ n : ℕ, f (a ^ n) ∉ q.asIdeal := by
    intro n hmem
    apply hfa
    apply q.isPrime.mem_of_pow_mem _
    simpa using hmem
  have hunit : ∀ y : Submonoid.powers a,
      IsUnit ((algebraMap S (Localization.AtPrime q.asIdeal)) (f y)) := by
    intro y
    exact IsLocalization.map_units (Localization.AtPrime q.asIdeal)
      (⟨f y, by
        rcases y with ⟨x, hx⟩
        rcases hx with ⟨n, rfl⟩
        show f (a ^ n) ∉ q.asIdeal
        exact hpow n⟩ : q.asIdeal.primeCompl)
  let β : Localization (Submonoid.powers a) →+*
      Localization.AtPrime q.asIdeal :=
    IsLocalization.lift (M := Submonoid.powers a)
      (g := (algebraMap S (Localization.AtPrime q.asIdeal)).comp f) hunit
  let : Algebra (Localization (Submonoid.powers a))
      (Localization.AtPrime q.asIdeal) := β.toAlgebra
  have hβ : β.comp (algebraMap R (Localization (Submonoid.powers a))) =
      (algebraMap S (Localization.AtPrime q.asIdeal)).comp f := by
    simp [β]
  let : IsScalarTower R (Localization (Submonoid.powers a))
      (Localization.AtPrime q.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' hβ.symm
  have hsource :
      Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal) ↔
        Algebra.QuasiFinite (Localization (Submonoid.powers a))
          (Localization.AtPrime q.asIdeal) := by
    constructor
    · intro h
      let : Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal) := h
      exact Algebra.QuasiFinite.of_restrictScalars R
        (Localization (Submonoid.powers a)) (Localization.AtPrime q.asIdeal)
    · intro h
      let : Algebra.QuasiFinite (Localization (Submonoid.powers a))
          (Localization.AtPrime q.asIdeal) := h
      let : Algebra.QuasiFinite R (Localization (Submonoid.powers a)) := hbase
      exact Algebra.QuasiFinite.trans R
        (Localization (Submonoid.powers a)) (Localization.AtPrime q.asIdeal)
  have hfa_mul : f a * b ∉ q.asIdeal := by
    intro hprod
    rcases q.isPrime.mem_or_mem hprod with hfa' | hb'
    · exact hfa hfa'
    · exact hb hb'
  have hdisj : Disjoint (Submonoid.powers (f a * b) : Set S) q.asIdeal := by
    apply Set.disjoint_left.2
    intro x hxS hxq
    rcases hxS with ⟨n, rfl⟩
    exact hfa_mul (q.isPrime.mem_of_pow_mem _ hxq)
  have hqmap : q'.asIdeal = q.asIdeal.map (algebraMap S T) := by
    simp [q', T, localizedPrimeAwayMul,
      Formalization.Books.Algebra.Unit17.standardOpenSpectrumInverse]
  have hmap :
      (q.asIdeal.map (algebraMap S T)).comap (algebraMap S T) = q.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers (f a * b)) T q.isPrime hdisj
  have hqcomap : q.asIdeal = q'.asIdeal.comap (algebraMap S T) := by
    rw [hqmap, hmap]
  have hqcomap' : q.asIdeal =
      q'.asIdeal.comap
        (algebraMap S (Localization (Submonoid.powers (f a * b)))) := by
    simpa [T] using hqcomap
  have hqf_eq :
      Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal) ↔
        Algebra.QuasiFinite R
          (@Localization.AtPrime S _ (q'.asIdeal.comap
            (algebraMap S (Localization (Submonoid.powers (f a * b)))))
            (q'.isPrime.comap
              (algebraMap S (Localization (Submonoid.powers (f a * b)))))) := by
    exact hqcomap'.rec
      (motive := fun I _ => ∀ hI : I.IsPrime,
        Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal) ↔
          Algebra.QuasiFinite R (@Localization.AtPrime S _ I hI))
      (by intro hI; rfl)
      (q'.isPrime.comap
        (algebraMap S (Localization (Submonoid.powers (f a * b)))))
  have e0 :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Submonoid.powers (f a * b)) q'.asIdeal
  have eR := e0.restrictScalars R
  have heqR :
      Algebra.QuasiFinite R
          (@Localization.AtPrime S _ (q'.asIdeal.comap
            (algebraMap S (Localization (Submonoid.powers (f a * b)))))
            (q'.isPrime.comap
              (algebraMap S (Localization (Submonoid.powers (f a * b)))))) ↔
        Algebra.QuasiFinite R (Localization.AtPrime q'.asIdeal) :=
    Algebra.QuasiFinite.iff_of_algEquiv eR
  have htransport :
      Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal) ↔
        Algebra.QuasiFinite R (Localization.AtPrime q'.asIdeal) :=
    hqf_eq.trans heqR
  have hα :
      α.comp (algebraMap R (Localization.Away a)) =
        (algebraMap S T).comp f := by
    ext r
    simp [α, T, Formalization.Books.Algebra.Unit30.localizationAwayMulMap]
  have hfmap : algebraMap R S = f := RingHom.algebraMap_toAlgebra f
  let : IsScalarTower R (Localization.Away a)
      (Localization.AtPrime q'.asIdeal) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      calc
        algebraMap R (Localization.AtPrime q'.asIdeal) r =
            algebraMap T (Localization.AtPrime q'.asIdeal)
              (algebraMap S T (f r)) := by
          calc
            algebraMap R (Localization.AtPrime q'.asIdeal) r =
                algebraMap S (Localization.AtPrime q'.asIdeal) (f r) := by
              simpa only [hfmap] using
                (IsScalarTower.algebraMap_apply R S
                  (Localization.AtPrime q'.asIdeal) r)
            _ = algebraMap T (Localization.AtPrime q'.asIdeal)
                  (algebraMap S T (f r)) := by
              exact (IsScalarTower.algebraMap_apply S
                (Localization (Submonoid.powers (f a * b)))
                (Localization.AtPrime q'.asIdeal) (f r)).symm
        _ = algebraMap T (Localization.AtPrime q'.asIdeal)
              (α (algebraMap R (Localization.Away a) r)) := by
          have hr := congrArg (fun z => z r) hα
          change α (algebraMap R (Localization.Away a) r) =
            algebraMap S T (f r) at hr
          exact congrArg (algebraMap T (Localization.AtPrime q'.asIdeal)) hr.symm)
  have htarget :
      Algebra.QuasiFinite R (Localization.AtPrime q'.asIdeal) ↔
        Algebra.QuasiFinite (Localization.Away a)
          (Localization.AtPrime q'.asIdeal) := by
    constructor
    · intro h
      let : Algebra.QuasiFinite R (Localization.AtPrime q'.asIdeal) := h
      exact Algebra.QuasiFinite.of_restrictScalars R
        (Localization.Away a) (Localization.AtPrime q'.asIdeal)
    · intro h
      let : Algebra.QuasiFinite (Localization.Away a)
          (Localization.AtPrime q'.asIdeal) := h
      let : Algebra.QuasiFinite R (Localization (Submonoid.powers a)) := hbase
      exact Algebra.QuasiFinite.trans R
        (Localization.Away a) (Localization.AtPrime q'.asIdeal)
  have hαfinite : RingHom.FiniteType α := by
    have hloc : RingHom.FiniteType (algebraMap S T) := by
      exact RingHom.finiteType_algebraMap.mpr inferInstance
    have hcomp : RingHom.FiniteType ((algebraMap S T).comp f) :=
      hloc.comp hfinite
    have hcomp_eq :
        α.comp (algebraMap R (Localization.Away a)) =
          (algebraMap S T).comp f := hα
    apply RingHom.FiniteType.of_comp_finiteType
      (f := algebraMap R (Localization.Away a))
    rw [hcomp_eq]
    exact hcomp
  change (RingHom.FiniteType f ∧
      Algebra.QuasiFinite R (Localization.AtPrime q.asIdeal)) ↔
    (RingHom.FiniteType α ∧
      Algebra.QuasiFinite (Localization.Away a)
        (Localization.AtPrime q'.asIdeal))
  constructor
  · rintro ⟨_, hqf⟩
    exact ⟨hαfinite, htarget.mp (htransport.mp hqf)⟩
  · rintro ⟨_, hqf⟩
    exact ⟨hfinite, htransport.mpr (htarget.mpr hqf)⟩

/- The four-ring diagram uses the canonical tensor-product map already
   supplied by Chapter 99. -/
theorem quasiFiniteAt_of_surjective_tensorProduct
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (h : S →+* S') (k : R' →+* S')
    (compat : h.comp f = k.comp g)
    (hfinite : RingHom.FiniteType f)
    (hsurj : Function.Surjective
      (Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
        f g h k compat))
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (p' : PrimeSpectrum R') (q' : PrimeSpectrum S')
    (hqp : PrimeSpectrum.comap f q = p)
    (hp'p : PrimeSpectrum.comap g p' = p)
    (hq'q : PrimeSpectrum.comap h q' = q)
    (hq'p' : PrimeSpectrum.comap k q' = p')
    (hq : IsQuasiFiniteAt f q) :
    IsQuasiFiniteAt k q' := by
  classical
  have _hqp : PrimeSpectrum.comap f q = p := hqp
  have _hp'p : PrimeSpectrum.comap g p' = p := hp'p
  have _hq'p' : PrimeSpectrum.comap k q' = p' := hq'p'
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let : Algebra R S' := (h.comp f).toAlgebra
  let : Algebra R' S' := k.toAlgebra
  let : Algebra R' (S ⊗[R] R') :=
    (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g).toAlgebra
  let T := R' ⊗[R] S
  let e : T ≃ₐ[R'] S ⊗[R] R' :=
    Algebra.TensorProduct.commRight R R' S
  let φ := Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
    f g h k compat
  let φ' : T →+* S' := φ.comp e.toRingHom
  let iL : R' →+* T :=
    (Algebra.TensorProduct.includeLeft (R := R) (S := R')
      (A := R') (B := S)).toRingHom
  let iR : S →+* T :=
    (Algebra.TensorProduct.includeRight (R := R) (A := R')
      (B := S)).toRingHom
  have hφ' : Function.Surjective φ' := by
    exact hsurj.comp e.surjective
  have hφ'comp : φ'.comp iL = k := by
    ext x
    change φ (Algebra.TensorProduct.commRight R R' S (x ⊗ₜ[R] 1)) = k x
    rw [Algebra.TensorProduct.commRight_tmul]
    simp [φ, Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget]
  have hφ'h : φ'.comp iR = h := by
    ext x
    change φ (Algebra.TensorProduct.commRight R R' S (1 ⊗ₜ[R] x)) = h x
    rw [Algebra.TensorProduct.commRight_tmul]
    simp [φ, Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget]
  let qT : Ideal T := q'.asIdeal.comap φ'
  have hqT : q.asIdeal = qT.comap iR := by
    dsimp only [qT]
    rw [← Ideal.comap_comap]
    change q.asIdeal = q'.asIdeal.comap (φ'.comp iR)
    rw [hφ'h]
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal hq'q).symm
  let : Algebra R' T := Algebra.TensorProduct.leftAlgebra
  let : Algebra T S' := φ'.toAlgebra
  let : IsScalarTower R' T S' := IsScalarTower.of_algebraMap_eq' (by
    change k = φ'.comp iL
    exact hφ'comp.symm)
  let : q'.asIdeal.LiesOver qT := ⟨rfl⟩
  let : Algebra.QuasiFiniteAt R q.asIdeal := hq.2
  have hqbase : Algebra.QuasiFiniteAt R' qT :=
    Algebra.QuasiFiniteAt.baseChange q.asIdeal qT hqT
  let : Algebra.QuasiFiniteAt R' qT := hqbase
  have hqtarget : Algebra.QuasiFiniteAt R' q'.asIdeal :=
    Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver qT
      (RingHom.surjectiveOnStalks_of_surjective hφ') q'.asIdeal
  have hftT : RingHom.FiniteType (algebraMap R' T) := by
    exact RingHom.finiteType_algebraMap.mpr (by
      let : Algebra.FiniteType R S := hfinite
      infer_instance)
  have hft' : RingHom.FiniteType (φ'.comp iL) :=
    RingHom.FiniteType.comp_surjective hftT hφ'
  exact ⟨(by simpa [hφ'comp] using hft'), hqtarget⟩

theorem isQuasiFinite_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsQuasiFinite f) (hg : IsQuasiFinite g) :
    IsQuasiFinite (g.comp f) := by
  classical
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  have hQF_f : RingHom.QuasiFinite f := by
    rw [RingHom.QuasiFinite]
    constructor
    intro p hp
    let p' : PrimeSpectrum A := ⟨p, hp⟩
    exact (isQuasiFinite_iff_finite_fibres f hf.1).mp hf p'
  have hQF_g : RingHom.QuasiFinite g := by
    rw [RingHom.QuasiFinite]
    constructor
    intro p hp
    let p' : PrimeSpectrum B := ⟨p, hp⟩
    exact (isQuasiFinite_iff_finite_fibres g hg.1).mp hg p'
  have hQF : RingHom.QuasiFinite (g.comp f) := hQF_g.comp hQF_f
  refine ⟨RingHom.FiniteType.comp hg.1 hf.1, ?_⟩
  intro q
  change Algebra.QuasiFinite A (Localization.AtPrime q.asIdeal)
  let : Algebra.QuasiFinite A C := hQF
  exact Algebra.QuasiFinite.of_isLocalization (R := A)
    (S := C) q.asIdeal.primeCompl

theorem isQuasiFinite_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    ({q' : PrimeSpectrum (S ⊗[R] R') |
        IsQuasiFiniteAt
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) q'} :
        Set (PrimeSpectrum (S ⊗[R] R'))) =
      (PrimeSpectrum.comap
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) ⁻¹'
        {q : PrimeSpectrum S | IsQuasiFiniteAt f q} ∧
      (Function.Surjective (PrimeSpectrum.comap g) →
        (IsQuasiFinite f ↔
          IsQuasiFinite
            (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g))) ∧
      (IsQuasiFinite f →
        IsQuasiFinite
          (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g)) := by
  classical
  let : Algebra R S := f.toAlgebra
  let : Algebra R R' := g.toAlgebra
  let B := S ⊗[R] R'
  let h : S →+* B :=
    Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g
  let k : R' →+* B :=
    Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
  let : Algebra R' B := k.toAlgebra
  have hcomp : h.comp f = k.comp g := by
    change Algebra.TensorProduct.includeLeftRingHom.comp f =
      Algebra.TensorProduct.includeRight.toRingHom.comp g
    rw [← RingHom.algebraMap_toAlgebra f, ← RingHom.algebraMap_toAlgebra g]
    exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  have hφ :
      Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
          f g h k hcomp = RingHom.id B := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x : 1
      change (Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
        f g h k hcomp) (x ⊗ₜ[R] 1) = x ⊗ₜ[R] 1
      dsimp [Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget]
      simp [h, Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap]
      rfl
    · ext x : 1
      change (Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
        f g h k hcomp) (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] x
      dsimp [Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget]
      simp [k, Formalization.Books.Algebra.Unit14.baseChangeRingMap]
  have hsurj : Function.Surjective
      (Formalization.Books.Algebra.Unit99.tensorProductToSquareTarget
        f g h k hcomp) := by
    rw [hφ]
    exact Function.surjective_id
  have hfinite' : RingHom.FiniteType k := by
    exact Formalization.Books.Algebra.Unit14.baseChange_finite_type f g hfinite
  let : Algebra.FiniteType R S := hfinite
  let : Algebra.FiniteType R' B := hfinite'
  have hpoint_forward : ∀ q' : PrimeSpectrum B,
      IsQuasiFiniteAt f (PrimeSpectrum.comap h q') →
        IsQuasiFiniteAt k q' := by
    intro q' hq
    let q : PrimeSpectrum S := PrimeSpectrum.comap h q'
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap k q'
    have hp'p : PrimeSpectrum.comap g p' = p := by
      rw [← PrimeSpectrum.comap_comp_apply]
      rw [← hcomp]
      rfl
    exact quasiFiniteAt_of_surjective_tensorProduct f g h k hcomp hfinite
      hsurj p q p' q' rfl hp'p rfl rfl hq
  have hpoint_reverse : ∀ q' : PrimeSpectrum B,
      IsQuasiFiniteAt k q' →
        IsQuasiFiniteAt f (PrimeSpectrum.comap h q') := by
    intro q' hq'
    let q : PrimeSpectrum S := PrimeSpectrum.comap h q'
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q
    let p' : PrimeSpectrum R' := PrimeSpectrum.comap k q'
    have hp'p : PrimeSpectrum.comap g p' = p := by
      rw [← PrimeSpectrum.comap_comp_apply]
      rw [← hcomp]
      rfl
    have hqz : PrimeSpectrum.comap (algebraMap R S) q = p := by
      simp [q, p, RingHom.algebraMap_toAlgebra]
    have hq'z : PrimeSpectrum.comap (algebraMap R' B) q' = p' := by
      simp [p', RingHom.algebraMap_toAlgebra]
    let qF := Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hqz
    let qF' := Formalization.Books.Algebra.Unit112.tensorFibrePrime k p' q' hq'z
    have hqF : qF.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
      have hleft :=
        (PrimeSpectrum.preimageEquivFiber R S p).left_inv
          (⟨q, hqz⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
      exact congr($(hleft).1.asIdeal)
    have hqF' : qF'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q'.asIdeal := by
      have hleft :=
        (PrimeSpectrum.preimageEquivFiber R' B p').left_inv
          (⟨q', hq'z⟩ : PrimeSpectrum.comap (algebraMap R' B) ⁻¹' {p'})
      exact congr($(hleft).1.asIdeal)
    let : q.asIdeal.LiesOver p.asIdeal := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
        (congrArg PrimeSpectrum.asIdeal hqz).symm
    let : p'.asIdeal.LiesOver p.asIdeal := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
        (congrArg PrimeSpectrum.asIdeal hp'p).symm
    let : q'.asIdeal.LiesOver p'.asIdeal := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
        (congrArg PrimeSpectrum.asIdeal hq'z).symm
    have hqf_iff_dim_f :
        IsQuasiFiniteAt f q ↔
          Formalization.Books.Topology.Unit10.krullDimensionAt qF = 0 := by
      constructor
      · intro hqf
        let : Algebra.QuasiFiniteAt R q.asIdeal := hqf.2
        let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal :=
          Algebra.QuasiFiniteAt.baseChange q.asIdeal qF.asIdeal hqF.symm
        have hlocal : Module.Finite p.asIdeal.ResidueField
            (Localization.AtPrime qF.asIdeal) :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p.asIdeal.ResidueField)
            (S := Localization.AtPrime qF.asIdeal)).mp inferInstance
        exact (isolated_point_fibre_criteria f p q hqz hfinite).out 1 3 |>.mp hlocal
      · intro hdim
        have hlocal : Module.Finite p.asIdeal.ResidueField
            (Localization.AtPrime qF.asIdeal) :=
          (isolated_point_fibre_criteria f p q hqz hfinite).out 3 1 |>.mp hdim
        let : Algebra.QuasiFiniteAt p.asIdeal.ResidueField qF.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p.asIdeal.ResidueField)
            (S := Localization.AtPrime qF.asIdeal)).mpr hlocal
        exact ⟨hfinite,
          Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
            p.asIdeal q.asIdeal qF.asIdeal hqF⟩
    have hqf_iff_dim_k :
        IsQuasiFiniteAt k q' ↔
          Formalization.Books.Topology.Unit10.krullDimensionAt qF' = 0 := by
      constructor
      · intro hqf
        let : Algebra.QuasiFiniteAt R' q'.asIdeal := hqf.2
        let : Algebra.QuasiFiniteAt p'.asIdeal.ResidueField qF'.asIdeal :=
          Algebra.QuasiFiniteAt.baseChange q'.asIdeal qF'.asIdeal hqF'.symm
        have hlocal : Module.Finite p'.asIdeal.ResidueField
            (Localization.AtPrime qF'.asIdeal) :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p'.asIdeal.ResidueField)
            (S := Localization.AtPrime qF'.asIdeal)).mp inferInstance
        exact (isolated_point_fibre_criteria k p' q' hq'z hfinite').out 1 3 |>.mp hlocal
      · intro hdim
        have hlocal : Module.Finite p'.asIdeal.ResidueField
            (Localization.AtPrime qF'.asIdeal) :=
          (isolated_point_fibre_criteria k p' q' hq'z hfinite').out 3 1 |>.mp hdim
        let : Algebra.QuasiFiniteAt p'.asIdeal.ResidueField qF'.asIdeal :=
          (Algebra.QuasiFinite.iff_of_isArtinianRing
            (R := p'.asIdeal.ResidueField)
            (S := Localization.AtPrime qF'.asIdeal)).mpr hlocal
        exact ⟨hfinite',
          Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField
            p'.asIdeal q'.asIdeal qF'.asIdeal hqF'⟩
    let K := p'.asIdeal.ResidueField
    let k₀ := p.asIdeal.ResidueField
    let : Algebra k₀ K :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' hp'p).toAlgebra
    let : IsScalarTower R k₀ K := by
      apply IsScalarTower.of_algebraMap_eq'
      ext r
      have hideal : p.asIdeal = p'.asIdeal.comap g := by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (congrArg PrimeSpectrum.asIdeal hp'p).symm
      change algebraMap R K r =
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal g hideal)
          (algebraMap R k₀ r)
      rw [Ideal.ResidueField.map_algebraMap]
      exact (IsScalarTower.algebraMap_apply R R' K r).symm
    let e₀ : K ⊗[R'] (R' ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R R' K K S
    let e₁ : K ⊗[k₀] (k₀ ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R k₀ K K S
    let c : K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[R'] (R' ⊗[R] S) :=
      Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K)
        (Algebra.TensorProduct.commRight R R' S).symm
    let e : K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[k₀] (k₀ ⊗[R] S) :=
      c.trans e₀ |>.trans e₁.symm
    have heinv : e.symm = e₁.trans (e₀.symm.trans c.symm) := by
      rfl
    have hc (a : K) (r' : R') (s : S) :
        c.symm (a ⊗ₜ[R'] (r' ⊗ₜ[R] s)) =
          a ⊗ₜ[R'] (s ⊗ₜ[R] r') := by
      rfl
    have heq (r : R) :
        e.symm.toRingHom (Algebra.TensorProduct.includeRight.toRingHom
          (algebraMap R (p.asIdeal.Fiber S) r)) =
          algebraMap R' (p'.asIdeal.Fiber B) (g r) := by
      change e.symm (Algebra.TensorProduct.includeRight
        (algebraMap R (p.asIdeal.Fiber S) r)) = _
      rw [heinv]
      simp only [AlgEquiv.trans_apply,
        Algebra.TensorProduct.includeRight_apply]
      change c.symm (e₀.symm (e₁
        (1 ⊗ₜ[k₀] ((algebraMap R k₀) r ⊗ₜ[R] (1 : S))))) = _
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
      simp only [Algebra.smul_def, mul_one]
      rw [hc]
      rw [← IsScalarTower.algebraMap_apply R k₀ K r]
      rw [IsScalarTower.algebraMap_apply R R' K r]
      simp only [Algebra.TensorProduct.algebraMap_apply]
      change (algebraMap R' K) (g r) ⊗ₜ[R'] (1 ⊗ₜ[R] 1) =
        (algebraMap R' K) (g r) ⊗ₜ[R'] 1
      rw [Algebra.TensorProduct.one_def]
    let qK : PrimeSpectrum (K ⊗[k₀] (k₀ ⊗[R] S)) :=
      PrimeSpectrum.comap e.symm.toRingHom qF'
    have hlyingK :
        PrimeSpectrum.comap
            (Algebra.TensorProduct.includeRight
              (R := k₀) (A := K) (B := k₀ ⊗[R] S)).toRingHom qK = qF := by
      rw [← PrimeSpectrum.comap_comp_apply]
      apply PrimeSpectrum.ext
      ext x
      obtain ⟨r, hr, s, hrs⟩ :=
        Ideal.Fiber.exists_smul_eq_one_tmul p.asIdeal x
      have hqFp :
          qF.asIdeal.comap (algebraMap R (p.asIdeal.Fiber S)) = p.asIdeal := by
        simpa [Ideal.under_def] using
          (Ideal.over_def qF.asIdeal p.asIdeal).symm
      have hnonF : algebraMap R (p.asIdeal.Fiber S) r ∉ qF.asIdeal := by
        intro hmem
        apply hr
        rw [← hqFp]
        exact hmem
      have hqFp' :
          qF'.asIdeal.comap (algebraMap R' (p'.asIdeal.Fiber B)) = p'.asIdeal := by
        simpa [Ideal.under_def] using
          (Ideal.over_def qF'.asIdeal p'.asIdeal).symm
      have hpideal : p'.asIdeal.comap g = p.asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using
          congrArg PrimeSpectrum.asIdeal hp'p
      have hnonT : algebraMap R (p.asIdeal.Fiber S) r ∉
          (PrimeSpectrum.comap
            (e.symm.toRingEquiv.toRingHom.comp
              Algebra.TensorProduct.includeRight.toRingHom) qF').asIdeal := by
        intro hmem
        have hmem' : algebraMap R' (p'.asIdeal.Fiber B) (g r) ∈ qF'.asIdeal := by
          rw [← heq r]
          exact hmem
        apply hr
        rw [← hpideal, ← hqFp']
        exact hmem'
      rw [← Ideal.IsPrime.mul_mem_left_iff hnonT,
        ← Ideal.IsPrime.mul_mem_left_iff hnonF]
      have hrs' : (algebraMap R (p.asIdeal.Fiber S) r) * x =
          1 ⊗ₜ[R] s := by
        simpa only [Algebra.smul_def] using hrs
      rw [hrs']
      change e.symm (Algebra.TensorProduct.includeRight
        (1 ⊗ₜ[R] s)) ∈ qF'.asIdeal ↔ 1 ⊗ₜ[R] s ∈ qF.asIdeal
      rw [heinv]
      simp only [AlgEquiv.trans_apply,
        Algebra.TensorProduct.includeRight_apply]
      rw [Algebra.TensorProduct.cancelBaseChange_tmul]
      rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
      rw [hc]
      simp only [Algebra.smul_def, map_one, mul_one]
      change (s ⊗ₜ[R] (1 : R')) ∈
          qF'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom ↔
        s ∈ qF.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
      rw [hqF', hqF]
      change h s ∈ q'.asIdeal ↔ s ∈ q.asIdeal
      simpa [q, h, PrimeSpectrum.comap_asIdeal]
    have hdim :
        Formalization.Books.Topology.Unit10.krullDimensionAt qF =
          Formalization.Books.Topology.Unit10.krullDimensionAt qK := by
      exact Formalization.Books.Algebra.Unit116.dimension_at_a_point_preserved_field_extension
        qF qK hlyingK
    have hdim_equiv {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
        (eXY : X ≃ₜ Y) (x : X) :
        Formalization.Books.Topology.Unit10.krullDimensionAt x =
          Formalization.Books.Topology.Unit10.krullDimensionAt (eXY x) := by
      rw [Formalization.Books.Topology.Unit10.krullDimensionAt,
        Formalization.Books.Topology.Unit10.krullDimensionAt]
      apply le_antisymm
      · refine le_iInf fun V => ?_
        let eXYc : C(X, Y) := ⟨eXY, eXY.continuous⟩
        let V' : TopologicalSpace.OpenNhdsOf (eXYc x) := by
          simpa [eXYc] using V
        let U : TopologicalSpace.OpenNhdsOf x :=
          TopologicalSpace.OpenNhdsOf.comap eXYc x V'
        have hdimUV :
            topologicalKrullDim (U : Set X) =
              topologicalKrullDim (V' : Set Y) := by
          let hUV := eXY.isEmbedding.homeomorphOfSubsetRange
            (s := (V' : Set Y)) (by intro y; simp)
          exact IsHomeomorph.topologicalKrullDim_eq hUV hUV.isHomeomorph
        calc
          (⨅ W : TopologicalSpace.OpenNhdsOf x,
              topologicalKrullDim (W : Set X)) ≤
              topologicalKrullDim (U : Set X) := iInf_le _ U
          _ = topologicalKrullDim (V : Set Y) := by
            simpa [U, V', eXYc] using hdimUV
      · refine le_iInf fun U => ?_
        let eXYsymmc : C(Y, X) := ⟨eXY.symm, eXY.symm.continuous⟩
        let U' : TopologicalSpace.OpenNhdsOf (eXYsymmc (eXY x)) :=
          { toOpens := U.toOpens
            mem' := by
              change eXYsymmc (eXY x) ∈ (U : Set X)
              simpa [eXYsymmc] using U.mem }
        let V : TopologicalSpace.OpenNhdsOf (eXY x) :=
          TopologicalSpace.OpenNhdsOf.comap eXYsymmc (eXY x) U'
        have hU' : (U' : Set X) = (U : Set X) := by
          ext z
          dsimp [U']
          rfl
        have hdimVU :
            topologicalKrullDim (V : Set Y) =
              topologicalKrullDim (U' : Set X) := by
          let hVU := eXY.symm.isEmbedding.homeomorphOfSubsetRange
            (s := (U' : Set X)) (by intro z; simp)
          exact IsHomeomorph.topologicalKrullDim_eq hVU hVU.isHomeomorph
        calc
          (⨅ W : TopologicalSpace.OpenNhdsOf (eXY x),
              topologicalKrullDim (W : Set Y)) ≤
              topologicalKrullDim (V : Set Y) := iInf_le _ V
          _ = topologicalKrullDim (U : Set X) := by
            rw [← hU']
            simpa [V, U', eXYsymmc] using hdimVU
    have hdim_equiv' :
        Formalization.Books.Topology.Unit10.krullDimensionAt qK =
          Formalization.Books.Topology.Unit10.krullDimensionAt qF' := by
      have h := hdim_equiv
        (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv) qF'
      have hqK' :
          PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv qF' = qK := by
        rfl
      rw [hqK'] at h
      exact h.symm
    exact hqf_iff_dim_f.mpr <| by
      rw [hdim, hdim_equiv']
      exact hqf_iff_dim_k.mp hq'
  have hset :
      ({q' : PrimeSpectrum B | IsQuasiFiniteAt k q'} : Set (PrimeSpectrum B)) =
        (PrimeSpectrum.comap h) ⁻¹'
          {q : PrimeSpectrum S | IsQuasiFiniteAt f q} := by
    ext q'
    constructor
    · exact hpoint_reverse q'
    · exact hpoint_forward q'
  have hglobal : IsQuasiFinite f → IsQuasiFinite k := by
    intro hfq
    refine ⟨hfinite', ?_⟩
    intro q'
    exact (hpoint_forward q' ⟨hfinite, hfq.2 (PrimeSpectrum.comap h q')⟩).2
  have hglobal_iff :
      Function.Surjective (PrimeSpectrum.comap g) →
        (IsQuasiFinite f ↔ IsQuasiFinite k) := by
    intro hsurj_g
    refine ⟨hglobal, ?_⟩
    intro hk
    refine ⟨hfinite, ?_⟩
    intro q
    let p : PrimeSpectrum R := PrimeSpectrum.comap f q
    obtain ⟨p', hp'p⟩ := hsurj_g p
    have hqz : PrimeSpectrum.comap (algebraMap R S) q = p := by
      simp [p, RingHom.algebraMap_toAlgebra]
    let K := p'.asIdeal.ResidueField
    let k₀ := p.asIdeal.ResidueField
    let : Algebra k₀ K :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' hp'p).toAlgebra
    let : IsScalarTower R k₀ K := by
      apply IsScalarTower.of_algebraMap_eq'
      ext r
      have hideal : p.asIdeal = p'.asIdeal.comap g := by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (congrArg PrimeSpectrum.asIdeal hp'p).symm
      change algebraMap R K r =
        (Ideal.ResidueField.map p.asIdeal p'.asIdeal g hideal)
          (algebraMap R k₀ r)
      rw [Ideal.ResidueField.map_algebraMap]
      exact (IsScalarTower.algebraMap_apply R R' K r).symm
    letI : IsField k₀ := Field.toIsField k₀
    letI : Module.Flat k₀ K :=
      RingHom.Flat.of_isField (R := k₀) (S := K) (Field.toIsField k₀)
        (algebraMap k₀ K)
    letI : Module.FaithfullyFlat k₀ K := by
      apply Module.FaithfullyFlat.of_comap_surjective
      intro P
      have hPbot : P.asIdeal = (⊥ : Ideal k₀) :=
        (Ideal.eq_bot_or_top P.asIdeal).resolve_right P.isPrime.ne_top
      refine ⟨⟨⊥, inferInstance⟩, ?_⟩
      apply PrimeSpectrum.ext
      rw [hPbot]
      change Ideal.comap (algebraMap k₀ K) (⊥ : Ideal K) = ⊥
      exact Ideal.comap_bot_of_injective _ (RingHom.injective _)
    letI : Algebra (k₀ ⊗[R] S) (K ⊗[k₀] (k₀ ⊗[R] S)) :=
      (Algebra.TensorProduct.includeRight
        (R := k₀) (A := K) (B := k₀ ⊗[R] S)).toRingHom.toAlgebra
    letI : Module.FaithfullyFlat (k₀ ⊗[R] S)
        (K ⊗[k₀] (k₀ ⊗[R] S)) :=
      Module.FaithfullyFlat.of_linearEquiv
        (k₀ ⊗[R] S) ((k₀ ⊗[R] S) ⊗[k₀] K)
        (Algebra.TensorProduct.commRight k₀ (k₀ ⊗[R] S) K).symm.toLinearEquiv
    let qF := Formalization.Books.Algebra.Unit112.tensorFibrePrime f p q hqz
    have hqF : qF.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
      have hleft :=
        (PrimeSpectrum.preimageEquivFiber R S p).left_inv
          (⟨q, hqz⟩ : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})
      exact congr($(hleft).1.asIdeal)
    let e₀ : K ⊗[R'] (R' ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R R' K K S
    let e₁ : K ⊗[k₀] (k₀ ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
      Algebra.TensorProduct.cancelBaseChange R k₀ K K S
    let c : K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[R'] (R' ⊗[R] S) :=
      Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K)
        (Algebra.TensorProduct.commRight R R' S).symm
    let e : K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[k₀] (k₀ ⊗[R] S) :=
      c.trans e₀ |>.trans e₁.symm
    have hc (a : K) (s : S) (r' : R') :
        c (a ⊗ₜ[R'] (s ⊗ₜ[R] r')) =
          a ⊗ₜ[R'] (r' ⊗ₜ[R] s) := by
      rfl
    obtain ⟨qK, hqK⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat
        (A := k₀ ⊗[R] S) (B := K ⊗[k₀] (k₀ ⊗[R] S)) qF
    have hmap :
        algebraMap (k₀ ⊗[R] S) (K ⊗[k₀] (k₀ ⊗[R] S)) =
          Algebra.TensorProduct.includeRight.toRingHom := by
      rfl
    have hqK' :
        qK.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = qF.asIdeal := by
      simpa only [PrimeSpectrum.comap_asIdeal, hmap] using
        congrArg PrimeSpectrum.asIdeal hqK
    let qF' := PrimeSpectrum.comap e.toRingHom qK
    let z := (PrimeSpectrum.preimageEquivFiber R' B p').symm qF'
    let q' : PrimeSpectrum B := z.1
    have hq'z : PrimeSpectrum.comap (algebraMap R' B) q' = p' := z.2
    have hqF' : qF'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom = q'.asIdeal := by
      change qF'.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom =
        (PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qF').asIdeal
      rfl
    have hqsource : PrimeSpectrum.comap h q' = q := by
      apply PrimeSpectrum.ext
      ext x
      change h x ∈ q'.asIdeal ↔ x ∈ q.asIdeal
      rw [← hqF']
      change Algebra.TensorProduct.includeRight.toRingHom (h x) ∈ qF'.asIdeal ↔
        x ∈ q.asIdeal
      change e (Algebra.TensorProduct.includeRight.toRingHom (h x)) ∈ qK.asIdeal ↔
        x ∈ q.asIdeal
      have heval :
          e (Algebra.TensorProduct.includeRight.toRingHom (h x)) =
            Algebra.TensorProduct.includeRight.toRingHom (1 ⊗ₜ[R] x) := by
        change e₁.symm (e₀ (c (1 ⊗ₜ[R'] (x ⊗ₜ[R] (1 : R'))))) =
          (1 : K) ⊗ₜ[k₀] (1 ⊗ₜ[R] x)
        rw [hc]
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        rw [Algebra.TensorProduct.cancelBaseChange_symm_tmul]
        simp only [Algebra.smul_def, one_mul, mul_one, map_one]
      rw [heval]
      rw [← Ideal.mem_comap, hqK', ← hqF]
      rfl
    rw [← hqsource]
    exact (hpoint_reverse q' ⟨hfinite', hk.2 q'⟩).2
  refine ⟨?_, hglobal_iff, hglobal⟩
  simpa [h, k, B] using hset

theorem quasiFiniteAt_of_finite_composite
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hfinite : RingHom.FiniteType (g.comp f))
    (p : PrimeSpectrum A) (q : PrimeSpectrum B) (r : PrimeSpectrum C)
    (hqp : PrimeSpectrum.comap f q = p)
    (hrq : PrimeSpectrum.comap g r = q)
    (hquasi : IsQuasiFiniteAt (g.comp f) r) :
    IsQuasiFiniteAt g r := by
  let : Algebra A B := f.toAlgebra
  let : Algebra B C := g.toAlgebra
  let : Algebra A C := (g.comp f).toAlgebra
  have hcompat : PrimeSpectrum.comap (g.comp f) r = p := by
    change PrimeSpectrum.comap f (PrimeSpectrum.comap g r) = p
    rw [hrq, hqp]
  have hqcomp : Algebra.QuasiFiniteAt A r.asIdeal :=
    (show PrimeSpectrum.comap (g.comp f) r = p ∧
        Algebra.QuasiFiniteAt A r.asIdeal from ⟨hcompat, hquasi.2⟩).2
  let : Algebra.QuasiFiniteAt A r.asIdeal := hqcomp
  let : IsScalarTower A B (Localization.AtPrime r.asIdeal) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    calc
      algebraMap A (Localization.AtPrime r.asIdeal) x =
          algebraMap C (Localization.AtPrime r.asIdeal) ((g.comp f) x) :=
        (IsScalarTower.algebraMap_apply A C (Localization.AtPrime r.asIdeal) x).symm
      _ = algebraMap C (Localization.AtPrime r.asIdeal) (g (f x)) := by rfl
      _ = algebraMap B (Localization.AtPrime r.asIdeal) (f x) :=
        IsScalarTower.algebraMap_apply B C (Localization.AtPrime r.asIdeal) (f x)
  have hqg : Algebra.QuasiFiniteAt B r.asIdeal :=
    Algebra.QuasiFinite.of_restrictScalars A B (Localization.AtPrime r.asIdeal)
  exact ⟨RingHom.FiniteType.of_comp_finiteType hfinite, hqg⟩

/- A minimal prime is represented by membership in the canonical
   `minimalPrimes` set, and the localized finite map is Mathlib's
   `Localization.awayMap`. -/
theorem exists_finite_localization_of_finite_fibre_over_minimal_prime
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (hp : p.asIdeal ∈ minimalPrimes R)
    (hfiniteType : RingHom.FiniteType f)
    (hfibre : Set.Finite
      {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p}) :
    ∃ a : R, a ∉ p.asIdeal ∧ RingHom.Finite (Localization.awayMap f a) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.FiniteType R S := hfiniteType
  let hset : (PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      ({p} : Set (PrimeSpectrum R))) =
      {q : PrimeSpectrum S | PrimeSpectrum.comap f q = p} := by
    ext q
    simp [RingHom.algebraMap_toAlgebra]
  let : Fintype {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} :=
    hfibre.fintype
  let : Fintype {q : PrimeSpectrum S // q ∈
      PrimeSpectrum.comap (algebraMap R S) ⁻¹' ({p} : Set (PrimeSpectrum R))} := by
    simpa [hset]
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  have hspec : Finite (PrimeSpectrum (p.asIdeal.Fiber S)) :=
    Finite.of_injective (f := e.symm) e.symm.injective
  have hmodule : Module.Finite p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
    (quasiFiniteAt_above_prime_criteria f p hfiniteType).out 2 1 |>.mp hspec
  have hall : ∀ q : PrimeSpectrum S, PrimeSpectrum.comap f q = p →
      IsQuasiFiniteAt f q :=
    (quasiFiniteAt_above_prime_criteria f p hfiniteType).out 1 0 |>.mp hmodule
  let A := integralClosure R S
  have hlocal (q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p}) :
      ∃ u : A, u.1 ∉ q.1.asIdeal ∧
        Function.Bijective (Localization.awayMap A.val.toRingHom u) := by
    let : q.1.asIdeal.LiesOver p.asIdeal := by
      rw [Ideal.liesOver_iff, Ideal.under_def]
      simpa [PrimeSpectrum.comap_asIdeal, RingHom.algebraMap_toAlgebra] using
        (congrArg PrimeSpectrum.asIdeal q.2).symm
    let : Algebra.QuasiFiniteAt R q.1.asIdeal := (hall q.1 q.2).2
    exact Algebra.ZariskisMainProperty.of_finiteType (R := R) q.1.asIdeal
  choose u huq hbij using hlocal
  let I : Ideal A := Ideal.span (Set.range u)
  have hnotle : ¬ I.comap (algebraMap R A) ≤ p.asIdeal := by
    intro hle
    have hpmin : p.asIdeal ∈ (I.comap (algebraMap R A)).minimalPrimes := by
      refine ⟨⟨hp.isPrime, hle⟩, ?_⟩
      intro r hr hle'
      exact hp.2 ⟨hr.1, bot_le⟩ hle'
    obtain ⟨Q, hQprime, hIQ, hQcomap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes
        (algebraMap R A) p hpmin
    let : Q.IsPrime := hQprime
    have hQmin : Q ∈ minimalPrimes A := by
      obtain ⟨Q₀, hQ₀min, hQ₀le⟩ :=
        Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := Q) bot_le
      let : Q₀.IsPrime := hQ₀min.isPrime
      have hQ₀under : Q₀.comap (algebraMap R A) = p.asIdeal := by
        apply le_antisymm
        · exact (Ideal.comap_mono hQ₀le).trans_eq hQcomap
        · have h₁ : Q₀.comap (algebraMap R A) ≤ p.asIdeal :=
            (Ideal.comap_mono hQ₀le).trans_eq hQcomap
          exact hp.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ h₁
      have hEq : Q₀ = Q := by
        by_contra hne
        have hlt : Q₀ < Q := lt_of_le_of_ne hQ₀le hne
        have hlt' := Ideal.IsIntegral.comap_lt_comap (R := R) (A := A) hlt
        rw [hQ₀under, hQcomap] at hlt'
        exact (lt_irrefl _ hlt')
      exact hEq ▸ hQ₀min
    obtain ⟨Q', hQ'prime, hQ'comap⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
        (FaithfulSMul.algebraMap_injective A S) Q hQmin
    let q' : PrimeSpectrum S := ⟨Q', hQ'prime⟩
    have hq'R : PrimeSpectrum.comap f q' = p := by
      apply PrimeSpectrum.ext
      change Q'.comap (algebraMap R S) = p.asIdeal
      calc
        Q'.comap (algebraMap R S) =
            (Q'.comap (algebraMap A S)).comap (algebraMap R A) := by
          rw [Ideal.comap_comap]
          rfl
        _ = Q.comap (algebraMap R A) := by rw [hQ'comap]
        _ = p.asIdeal := hQcomap
    let q₀ : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} :=
      ⟨q', hq'R⟩
    have huI : u q₀ ∈ I := by
      apply Ideal.subset_span
      exact ⟨q₀, rfl⟩
    have huQ : u q₀ ∈ Q := hIQ huI
    have huQ' : (u q₀).1 ∈ Q' := by
      have hmem : u q₀ ∈ Q'.comap (algebraMap A S) := by
        rw [hQ'comap]
        exact huQ
      simpa using hmem
    exact (huq q₀) huQ'
  obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hnotle
  let aA : A := algebraMap R A a
  let R₀ := Localization.Away (algebraMap R A a)
  have hmem_map :
      algebraMap A R₀ (algebraMap R A a) ∈
        Ideal.map (algebraMap A R₀) I :=
    Ideal.mem_map_of_mem _ haI
  have hmem_map' :
      algebraMap A R₀ (algebraMap R A a) ∈
        Ideal.span ((algebraMap A R₀) '' Set.range u) := by
    simpa [I, Ideal.map_span] using hmem_map
  have himage :
      (algebraMap A R₀) '' Set.range u =
        Set.range (fun q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} =>
          algebraMap A R₀ (u q)) := by
    ext x
    constructor
    · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨u q, ⟨q, rfl⟩, rfl⟩
  rw [himage] at hmem_map'
  have hmem :
      algebraMap A R₀ (algebraMap R A a) ∈
        Ideal.span (Set.range (fun q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} =>
          algebraMap A R₀ (u q))) :=
    hmem_map'
  have hspan :
      Ideal.span (Set.range (fun q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} =>
        algebraMap A R₀ (u q))) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ hmem
    exact IsLocalization.Away.algebraMap_isUnit _
  let fAS : A →ₐ[R] S := A.val
  have hsurj : Function.Surjective (Localization.awayMapₐ fAS aA) := by
    apply RingHom.surjective_ofLocalizationSpan
      (Localization.awayMapₐ fAS aA).toRingHom
      (Set.range (fun q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} =>
        algebraMap A R₀ (u q))) hspan
    rintro ⟨_, q, rfl⟩
    have hdvd : u q ∣ (algebraMap R A a) * u q := by
      exact ⟨algebraMap R A a, by simp [mul_comm]⟩
    have hmul : Function.Surjective
        (Localization.awayMap A.val.toRingHom
          ((algebraMap R A a) * (u q))) :=
      Localization.awayMap_surjective_of_dvd A.val.toRingHom hdvd (hbij q).2
    have hdouble := Localization.awayMap_awayMap_surjective
      A.val.toRingHom (algebraMap R A a) (u q) hmul
    have hbase :
        (Localization.awayMapₐ fAS aA).toRingHom =
          Localization.awayMap A.val.toRingHom (algebraMap R A a) := by
      ext x
      rfl
    rw [hbase]
    exact hdouble
  have ha0 : algebraMap R p.asIdeal.ResidueField a ≠ 0 := by
    simpa [Ideal.algebraMap_residueField_eq_zero] using ha
  have hu : IsUnit (algebraMap R p.asIdeal.ResidueField a) :=
    isUnit_iff_ne_zero.mpr ha0
  have hEq : (1 ⊗ₜ[R] aA : p.asIdeal.Fiber A) =
      algebraMap R (p.asIdeal.Fiber A) a := by
    rw [Algebra.TensorProduct.algebraMap_apply']
  have hgp : IsUnit (1 ⊗ₜ[R] aA : p.asIdeal.Fiber A) := by
    rw [hEq]
    have hmap := hu.map
      (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A))
    rw [← IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField
      (p.asIdeal.Fiber A) a] at hmap
    exact hmap
  obtain ⟨a', ha', hfin⟩ :=
    Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ
      fAS aA hsurj p.asIdeal hgp
  refine ⟨a', ha', ?_⟩
  have hbase' :
      (Localization.awayMapₐ (Algebra.ofId R S) a').toRingHom =
        Localization.awayMap f a' := by
    ext x
    rfl
  change RingHom.Finite
    (Localization.awayMapₐ (Algebra.ofId R S) a').toRingHom at hfin
  rw [hbase'] at hfin
  exact hfin

end

end Formalization.Books.Algebra.Unit122
