import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# More Algebra, Chapter 44: Permanence of properties under étale maps

This file records the local permanence results for an étale ring map.  Prime
localizations, Noetherian rings, Krull dimension, regular local rings,
Dedekind domains, and discrete valuation rings use Mathlib's canonical
interfaces.
-/

namespace Formalization.Books.MoreAlgebra.Unit44

universe u v

/- The introductory flatness facts are already covered by Mathlib's
`RingHom.Etale.iff_flat_and_formallyUnramified` and
`Module.FaithfullyFlat.of_flat_of_isLocalHom`; no chapter-specific aliases
are needed. -/

/-! ## Noetherian localizations -/

/-- An étale map preserves Noetherianity of corresponding prime localizations.
-/
theorem isNoetherianRing_localization_atPrime_iff_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    IsNoetherianRing (Localization.AtPrime p.asIdeal) ↔
      IsNoetherianRing (Localization.AtPrime q.asIdeal) := by
  have hpq' : p.asIdeal = q.asIdeal.comap f := by
    simpa using congrArg PrimeSpectrum.asIdeal hpq.symm
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hpq'
  have hflat : g.Flat := by
    exact RingHom.Flat.localRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
      q.asIdeal p.asIdeal hpq'
  have hfess : f.EssFiniteType := by
    change @Algebra.EssFiniteType A B _ _ f.toAlgebra
    letI : Algebra A B := f.toAlgebra
    letI : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g, hpq']
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    letI : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    letI : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.EssFiniteType A B := hfess
    letI : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    letI : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    letI : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    letI : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    letI : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    letI : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  constructor
  · intro h
    letI : IsNoetherianRing (Localization.AtPrime p.asIdeal) := h
    letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      g.toAlgebra
    letI : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := hgess
    exact Algebra.EssFiniteType.isNoetherianRing
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
  · intro h
    letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) := h
    letI : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      g.toAlgebra
    letI : Module.Flat (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := hflat
    letI : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal)) := by
      change IsLocalHom g
      exact Localization.isLocalHom_localRingHom
        (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq'
    letI : Module.FaithfullyFlat (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    apply Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (R := Localization.AtPrime p.asIdeal)
      (M := Localization.AtPrime p.asIdeal)
      (A := Localization.AtPrime q.asIdeal)
    exact isNoetherian_of_linearEquiv
      (Algebra.TensorProduct.rid (R := Localization.AtPrime p.asIdeal)
        (S := Localization.AtPrime q.asIdeal)
        (A := Localization.AtPrime q.asIdeal)).symm.toLinearEquiv

/-! ## Local dimension -/

/-- Corresponding prime localizations of an étale map have equal Krull
dimension. -/
theorem ringKrullDim_localization_atPrime_eq_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    ringKrullDim (Localization.AtPrime p.asIdeal) =
      ringKrullDim (Localization.AtPrime q.asIdeal) := by
  have hpq' : p.asIdeal = q.asIdeal.comap f := by
    simpa using congrArg PrimeSpectrum.asIdeal hpq.symm
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hpq'
  have hflat : g.Flat := by
    exact RingHom.Flat.localRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
      q.asIdeal p.asIdeal hpq'
  have hfess : f.EssFiniteType := by
    change @Algebra.EssFiniteType A B _ _ f.toAlgebra
    letI : Algebra A B := f.toAlgebra
    letI : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g, hpq']
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    letI : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    letI : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.EssFiniteType A B := hfess
    letI : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    letI : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    letI : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    letI : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    letI : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    letI : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  letI : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := g.toAlgebra
  letI : Module.Flat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hflat
  letI : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom g
    exact Localization.isLocalHom_localRingHom
      (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq'
  letI : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hgess
  letI : Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    letI : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    letI : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    letI : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    letI : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap B (Localization.AtPrime q.asIdeal) (f x) =
        g (algebraMap A (Localization.AtPrime p.asIdeal) x)
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal f hpq' x).symm
    letI : Algebra.FormallyUnramified A B := by
      change @Algebra.FormallyUnramified A B _ _ f.toAlgebra
      exact hf.formallyUnramified
    letI : Algebra.FormallyUnramified B (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.of_isLocalization q.asIdeal.primeCompl
    letI : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.comp A B (Localization.AtPrime q.asIdeal)
    exact Algebra.FormallyUnramified.localization_base p.asIdeal.primeCompl
  letI : Algebra.QuasiFinite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := inferInstance
  have hstrict : StrictMono
      (PrimeSpectrum.comap (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal))) := by
    intro x y hxy
    have hle : x.asIdeal ≤ y.asIdeal := hxy.le
    have hcomap :
        (x.comap (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal))).asIdeal ≤
          (y.comap (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal))).asIdeal := by
      exact Ideal.comap_mono hle
    have hle' :
        x.comap (algebraMap (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal)) ≤
          y.comap (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)) :=
      hcomap
    refine lt_of_le_of_ne hle' ?_
    intro heq
    apply hxy.ne
    apply PrimeSpectrum.ext
    apply Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := Localization.AtPrime p.asIdeal)
      (S := Localization.AtPrime q.asIdeal) x.asIdeal y.asIdeal hle
    simpa [Ideal.under_def] using congrArg PrimeSpectrum.asIdeal heq
  have hle : ringKrullDim (Localization.AtPrime q.asIdeal) ≤
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
    exact Order.krullDim_le_of_strictMono _ hstrict
  have hmap :
      (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).map
          (algebraMap (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime q.asIdeal)) =
        IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) :=
    Algebra.FormallyUnramified.map_maximalIdeal
  letI : Algebra.HasGoingDown (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := inferInstance
  have hge : ringKrullDim (Localization.AtPrime p.asIdeal) ≤
      ringKrullDim (Localization.AtPrime q.asIdeal) := by
    change Order.krullDim (PrimeSpectrum (Localization.AtPrime p.asIdeal)) ≤
      Order.krullDim (PrimeSpectrum (Localization.AtPrime q.asIdeal))
    rw [Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
    apply WithBot.coe_le_coe.mpr
    refine iSup_le fun l ↦ ?_
    obtain ⟨P, hPle, hPprime, hPover⟩ :=
      Ideal.exists_ideal_le_liesOver_of_le
        (Q := IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
        (p := l.last.asIdeal)
        (q := IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (by exact IsLocalRing.le_maximalIdeal_of_isPrime _)
    letI : P.IsPrime := hPprime
    letI : P.LiesOver l.last.asIdeal := hPover
    obtain ⟨l', hlen, _, _⟩ :=
      Ideal.exists_ltSeries_of_hasGoingDown l P
    calc
      (l.length : ℕ∞) = (l'.length : ℕ∞) := by rw [hlen]
      _ ≤ ⨆ (l' : LTSeries (PrimeSpectrum (Localization.AtPrime q.asIdeal))),
          (l'.length : ℕ∞) := le_iSup (fun l' : LTSeries
            (PrimeSpectrum (Localization.AtPrime q.asIdeal)) ↦ (l'.length : ℕ∞)) l'
  exact le_antisymm hge hle

/-! ## Regular local rings -/

/-- Corresponding prime localizations of an étale map are regular local rings
simultaneously. -/
theorem isRegularLocalRing_localization_atPrime_iff_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  sorry

/-! ## Dedekind domains -/

/-- A ring is a finite product of Dedekind domains when it is ring-isomorphic
to a finite product of commutative Dedekind domains.

The bundled `CommRingCat` factors retain their ring structures while the
finite index type records that this is a finite product. -/
def IsFiniteProductOfDedekindDomains
    (B : Type v) [CommRing B] : Prop :=
  ∃ (ι : Type v) (hι : Fintype ι) (S : ι → CommRingCat.{v}),
    letI : Fintype ι := hι
    (∀ i, IsDedekindDomain (S i)) ∧
      Nonempty (B ≃+* (∀ i, (S i : Type v)))

/-- An étale extension of a Dedekind domain is a finite product of Dedekind
domains. -/
theorem isFiniteProductOfDedekindDomains_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A] :
    IsFiniteProductOfDedekindDomains B := by
  sorry

/-- A localization at a maximal ideal lying over a nonzero prime of an étale
extension of a Dedekind domain is a discrete valuation ring.

The nonzero-prime hypothesis is needed because Mathlib's discrete valuation
ring notion excludes fields. -/
theorem isDiscreteValuationRing_localization_atPrime_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A] :
    ∀ q : MaximalSpectrum B,
      q.asIdeal.comap f ≠ ⊥ →
      ∃ hq : IsDomain (Localization.AtPrime q.asIdeal),
        @IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) _ hq := by
  sorry

end Formalization.Books.MoreAlgebra.Unit44
