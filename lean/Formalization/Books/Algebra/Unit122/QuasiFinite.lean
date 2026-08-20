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
  sorry

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
  sorry

theorem isQuasiFinite_comp
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hf : IsQuasiFinite f) (hg : IsQuasiFinite g) :
    IsQuasiFinite (g.comp f) := by
  sorry

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
  sorry

theorem quasiFiniteAt_of_finite_composite
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (hfinite : RingHom.FiniteType (g.comp f))
    (p : PrimeSpectrum A) (q : PrimeSpectrum B) (r : PrimeSpectrum C)
    (hqp : PrimeSpectrum.comap f q = p)
    (hrq : PrimeSpectrum.comap g r = q)
    (hquasi : IsQuasiFiniteAt (g.comp f) r) :
    IsQuasiFiniteAt g r := by
  sorry

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
  sorry

end

end Formalization.Books.Algebra.Unit122
