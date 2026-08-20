import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Unramified.Dedekind
import Formalization.Books.Algebra.Unit37.NormalRings

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
    let : Algebra A B := f.toAlgebra
    let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g]
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A B := hfess
    let : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    let : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  constructor
  · intro h
    let : IsNoetherianRing (Localization.AtPrime p.asIdeal) := h
    let : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      g.toAlgebra
    let : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := hgess
    exact Algebra.EssFiniteType.isNoetherianRing
      (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)
  · intro h
    let : IsNoetherianRing (Localization.AtPrime q.asIdeal) := h
    let : Algebra (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
      g.toAlgebra
    let : Module.Flat (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := hflat
    let : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal)) := by
      change IsLocalHom g
      exact Localization.isLocalHom_localRingHom
        (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq'
    let : Module.FaithfullyFlat (Localization.AtPrime p.asIdeal)
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
    let : Algebra A B := f.toAlgebra
    let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g]
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A B := hfess
    let : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    let : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  let : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := g.toAlgebra
  let : Module.Flat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hflat
  let : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom g
    exact Localization.isLocalHom_localRingHom
      (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq'
  let : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hgess
  let : Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap B (Localization.AtPrime q.asIdeal) (f x) =
        g (algebraMap A (Localization.AtPrime p.asIdeal) x)
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal f hpq' x).symm
    let : Algebra.FormallyUnramified A B := by
      change @Algebra.FormallyUnramified A B _ _ f.toAlgebra
      exact hf.formallyUnramified
    let : Algebra.FormallyUnramified B (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.of_isLocalization q.asIdeal.primeCompl
    let : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.comp A B (Localization.AtPrime q.asIdeal)
    exact Algebra.FormallyUnramified.localization_base p.asIdeal.primeCompl
  let : Algebra.QuasiFinite (Localization.AtPrime p.asIdeal)
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
  let : Algebra.HasGoingDown (Localization.AtPrime p.asIdeal)
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
    let : P.IsPrime := hPprime
    let : P.LiesOver l.last.asIdeal := hPover
    obtain ⟨l', hlen, _, _⟩ :=
      Ideal.exists_ltSeries_of_hasGoingDown l P
    calc
      (l.length : ℕ∞) = (l'.length : ℕ∞) := by rw [hlen]
      _ ≤ ⨆ (l' : LTSeries (PrimeSpectrum (Localization.AtPrime q.asIdeal))),
          (l'.length : ℕ∞) := le_iSup (fun l' : LTSeries
            (PrimeSpectrum (Localization.AtPrime q.asIdeal)) ↦ (l'.length : ℕ∞)) l'
  exact le_antisymm hge hle

/-! ## Regular local rings -/

private theorem spanFinrank_maximalIdeal_eq_of_flat_of_formallyUnramified
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    (IsLocalRing.maximalIdeal R).spanFinrank =
      (IsLocalRing.maximalIdeal S).spanFinrank := by
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let mR := IsLocalRing.maximalIdeal R
  let mS := IsLocalRing.maximalIdeal S
  have hmax : mR.map (algebraMap R S) = mS := by
    exact Algebra.FormallyUnramified.map_maximalIdeal
  have hle : mS.spanFinrank ≤ mR.spanFinrank := by
    rw [← hmax]
    exact Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
      mR.fg_of_isNoetherianRing
  let iota : mR → mS := fun x =>
    ⟨algebraMap R S x, by rw [← hmax]; exact Ideal.mem_map_of_mem _ x.2⟩
  have hiota : Submodule.span S (Set.range iota) = ⊤ := by
    rw [← (Submodule.map_injective_of_injective
      (Submodule.injective_subtype mS)).eq_iff,
      Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have hset : Submodule.subtype mS '' Set.range iota =
        Set.range (fun x : mR => (algebraMap R S (x : R))) := by
      ext z
      constructor
      · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨iota x, ⟨x, rfl⟩, rfl⟩
    rw [hset, Ideal.submodule_span_eq]
    have hset' : Set.range (fun x : mR => (algebraMap R S (x : R))) =
        algebraMap R S '' (mR : Set R) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [hset', ← Ideal.map_span, Ideal.span_eq]
    simpa using hmax
  have hcot : Submodule.span (IsLocalRing.ResidueField S)
      (mS.toCotangent '' Set.range iota) = ⊤ := by
    exact (IsLocalRing.CotangentSpace.span_image_eq_top_iff (R := S)).mpr hiota
  obtain ⟨t, ht, htspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq
      (IsLocalRing.ResidueField S)
      (mS.toCotangent '' Set.range iota)
  choose y hy hty using ht
  choose j hj using hy
  have hyt : mS.toCotangent '' Set.range y = Set.range t := by
    ext z
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (hty k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨y k, ⟨k, rfl⟩, hty k⟩
  have hyspan : Submodule.span S (Set.range y) = ⊤ := by
    apply (IsLocalRing.CotangentSpace.span_image_eq_top_iff (R := S)).mp
    have htop : Submodule.span (IsLocalRing.ResidueField S) (Set.range t) = ⊤ := by
      calc
        _ = Submodule.span (IsLocalRing.ResidueField S)
            (mS.toCotangent '' Set.range iota) := htspan
        _ = ⊤ := hcot
    rw [hyt]
    exact htop
  let j' : Fin (Module.finrank (IsLocalRing.ResidueField S)
      (Submodule.span (IsLocalRing.ResidueField S)
        (mS.toCotangent '' Set.range iota))) → R := fun k => j k
  let J : Ideal R := Ideal.span (Set.range j')
  have hJ : J.map (algebraMap R S) = mS := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      exact Ideal.span_le.2 (fun x hx => by
        obtain ⟨k, rfl⟩ := hx
        exact (iota (j k)).2)
    · have htop : (⊤ : Submodule S mS) ≤
          Submodule.comap (Submodule.subtype mS) (J.map (algebraMap R S)) := by
        rw [← hyspan]
        refine Submodule.span_le.2 (fun x hx => ?_)
        obtain ⟨k, rfl⟩ := hx
        rw [← hj k]
        exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self k))
      intro x hx
      change (⟨x, hx⟩ : mS) ∈
        Submodule.comap (Submodule.subtype mS) (J.map (algebraMap R S))
      exact htop Submodule.mem_top
  have hJ' : J = mR := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (A := R) (B := S) J, hJ,
      IsLocalRing.maximalIdeal_comap]
  have htc_eq : Module.finrank (IsLocalRing.ResidueField S)
      (Submodule.span (IsLocalRing.ResidueField S) (mS.toCotangent '' Set.range iota)) =
      mS.spanFinrank := by
    rw [hcot]
    simpa using (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace S).symm
  have hge : mR.spanFinrank ≤ mS.spanFinrank := by
    let : Fintype (Set.range j') := Fintype.ofFinite _
    calc
      mR.spanFinrank = J.spanFinrank := by rw [hJ']
      _ ≤ (Set.range j').ncard := by
        simpa [J] using (Submodule.spanFinrank_span_le_ncard_of_finite
          (Set.toFinite (Set.range j')))
      _ ≤ Fintype.card (Fin (Module.finrank (IsLocalRing.ResidueField S)
          (Submodule.span (IsLocalRing.ResidueField S)
            (mS.toCotangent '' Set.range iota)))) :=
        by
          simpa only [Set.fintypeCard_eq_ncard] using Fintype.card_range_le j'
      _ = Module.finrank (IsLocalRing.ResidueField S)
          (Submodule.span (IsLocalRing.ResidueField S)
            (mS.toCotangent '' Set.range iota)) := by simp
      _ = mS.spanFinrank := htc_eq
  exact le_antisymm hge hle

private theorem spanFinrank_maximalIdeal_eq_localization_atPrime_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p)
    [IsNoetherianRing (Localization.AtPrime p.asIdeal)]
    [IsNoetherianRing (Localization.AtPrime q.asIdeal)] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).spanFinrank =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank := by
  have hpq' : p.asIdeal = q.asIdeal.comap f := by
    simpa using congrArg PrimeSpectrum.asIdeal hpq.symm
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hpq'
  have hflat : g.Flat := by
    exact RingHom.Flat.localRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
      q.asIdeal p.asIdeal hpq'
  have hfess : f.EssFiniteType := by
    change @Algebra.EssFiniteType A B _ _ f.toAlgebra
    let : Algebra A B := f.toAlgebra
    let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g]
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A B := hfess
    let : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    let : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  let : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := g.toAlgebra
  let : Module.Flat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hflat
  let : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom g
    exact Localization.isLocalHom_localRingHom
      (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq'
  let : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hgess
  let : Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap B (Localization.AtPrime q.asIdeal) (f x) =
        g (algebraMap A (Localization.AtPrime p.asIdeal) x)
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal f hpq' x).symm
    let : Algebra.FormallyUnramified A B := hf.formallyUnramified
    let : Algebra.FormallyUnramified B (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.of_isLocalization q.asIdeal.primeCompl
    let : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.comp A B (Localization.AtPrime q.asIdeal)
    exact Algebra.FormallyUnramified.localization_base p.asIdeal.primeCompl
  exact spanFinrank_maximalIdeal_eq_of_flat_of_formallyUnramified

/-- Corresponding prime localizations of an étale map are regular local rings
simultaneously. -/
theorem isRegularLocalRing_localization_atPrime_iff_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f)
    (p : PrimeSpectrum A) (q : PrimeSpectrum B)
    (hpq : PrimeSpectrum.comap f q = p) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) ↔
      IsRegularLocalRing (Localization.AtPrime q.asIdeal) := by
  have hnoeth := isNoetherianRing_localization_atPrime_iff_of_etale f hf p q hpq
  constructor
  · intro hreg
    let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hreg
    let : IsNoetherianRing (Localization.AtPrime p.asIdeal) := inferInstance
    let : IsNoetherianRing (Localization.AtPrime q.asIdeal) := hnoeth.mp inferInstance
    let hspan := spanFinrank_maximalIdeal_eq_localization_atPrime_of_etale
      f hf p q hpq
    let hdim := ringKrullDim_localization_atPrime_eq_of_etale f hf p q hpq
    rw [isRegularLocalRing_iff] at hreg ⊢
    calc
      (↑(IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank :
          WithBot ℕ∞) =
          ↑(IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).spanFinrank := by
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hspan.symm
      _ = ringKrullDim (Localization.AtPrime p.asIdeal) := hreg
      _ = ringKrullDim (Localization.AtPrime q.asIdeal) := hdim
  · intro hreg
    let : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hreg
    let : IsNoetherianRing (Localization.AtPrime q.asIdeal) := inferInstance
    let : IsNoetherianRing (Localization.AtPrime p.asIdeal) := hnoeth.mpr inferInstance
    let hspan := spanFinrank_maximalIdeal_eq_localization_atPrime_of_etale
      f hf p q hpq
    let hdim := ringKrullDim_localization_atPrime_eq_of_etale f hf p q hpq
    rw [isRegularLocalRing_iff] at hreg ⊢
    calc
      (↑(IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).spanFinrank :
          WithBot ℕ∞) =
          ↑(IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank := by
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) hspan
      _ = ringKrullDim (Localization.AtPrime q.asIdeal) := hreg
      _ = ringKrullDim (Localization.AtPrime p.asIdeal) := hdim.symm

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

private theorem isDomain_of_isLocalRing_of_isNoetherianRing_of_isSMulRegular
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : IsSMulRegular R x)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span {x}) :
    IsDomain R := by
  classical
  have hzero : ∀ {a b : R}, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hb⟩ := hne
    let div : R → R := fun z =>
      if hz : z ∈ IsLocalRing.maximalIdeal R then
        Classical.choose (Ideal.mem_span_singleton.mp (hmax ▸ hz))
      else 0
    have div_spec {z : R} (hz : z ∈ IsLocalRing.maximalIdeal R) :
        z = x * div z := by
      dsimp [div]
      rw [dif_pos hz]
      exact (Classical.choose_spec
        (Ideal.mem_span_singleton.mp (hmax ▸ hz)))
    have hseq : ∀ n : ℕ, ∃ a' b' : R,
        a = x ^ n * a' ∧ b = x ^ n * b' ∧
          a' ≠ 0 ∧ b' ≠ 0 ∧ a' * b' = 0 := by
      intro n
      induction n with
      | zero =>
          refine ⟨a, b, by simp, by simp, ha, hb, hab⟩
      | succ n ih =>
          obtain ⟨a', b', ha', hb', ha0', hb0', hab'⟩ := ih
          have haM : a' ∈ IsLocalRing.maximalIdeal R := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            intro hunit
            exact hb0' (hunit.mul_left_cancel (by simpa only [mul_zero] using hab'))
          have hbM : b' ∈ IsLocalRing.maximalIdeal R := by
            rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
            intro hunit
            exact ha0' (hunit.mul_right_cancel (by simpa only [zero_mul] using hab'))
          have ha_div : a' = x * div a' := div_spec haM
          have hb_div : b' = x * div b' := div_spec hbM
          have hab_div : div a' * div b' = 0 := by
            have hab'' : (x * div a') * (x * div b') = 0 := by
              rw [ha_div, hb_div] at hab'
              exact hab'
            apply hx
            apply hx
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hab''
          have ha0_div : div a' ≠ 0 := by
            intro h
            apply ha0'
            rw [ha_div, h, mul_zero]
          have hb0_div : div b' ≠ 0 := by
            intro h
            apply hb0'
            rw [hb_div, h, mul_zero]
          refine ⟨div a', div b', ?_, ?_, ha0_div, hb0_div, hab_div⟩
          · calc
              a = x ^ n * a' := ha'
              _ = x ^ n * (x * div a') := congrArg (fun z => x ^ n * z) ha_div
              _ = x ^ (Nat.succ n) * div a' := by rw [pow_succ]; ring
          · calc
              b = x ^ n * b' := hb'
              _ = x ^ n * (x * div b') := congrArg (fun z => x ^ n * z) hb_div
              _ = x ^ (Nat.succ n) * div b' := by rw [pow_succ]; ring
    have hamem : ∀ n : ℕ, a ∈ IsLocalRing.maximalIdeal R ^ n := by
      intro n
      obtain ⟨a', _, ha', _, _, _⟩ := hseq n
      rw [ha']
      have hxpow : x ^ n ∈ IsLocalRing.maximalIdeal R ^ n := by
        rw [hmax]
        exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self x) n
      simpa [mul_comm] using (IsLocalRing.maximalIdeal R ^ n).mul_mem_left a'
        hxpow
    have hai : a ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n := by
      rw [Ideal.mem_iInf]
      exact hamem
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hai
    exact ha (by simpa using hai)
  refine { toIsCancelMulZero := ?_, toNontrivial := inferInstance }
  refine { mul_left_cancel_of_ne_zero := ?_, mul_right_cancel_of_ne_zero := ?_ }
  · intro a ha b c hab
    change a * b = a * c at hab
    have hbc : a * (b - c) = 0 := by
      rw [mul_sub, hab, sub_self]
    obtain h | h := hzero hbc
    · exact (ha h).elim
    · exact sub_eq_zero.mp h
  · intro b hb a c hab
    change a * b = c * b at hab
    have hbc : (a - c) * b = 0 := by
      rw [sub_mul, hab, sub_self]
    obtain h | h := hzero hbc
    · exact sub_eq_zero.mp h
    · exact (hb h).elim

private theorem isDedekindDomain_localization_atPrime_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A]
    [IsNoetherianRing B] (q : PrimeSpectrum B) :
    IsDedekindDomain (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum A := q.comap f
  have hpq : p.asIdeal = q.asIdeal.comap f := rfl
  let : Algebra A B := f.toAlgebra
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hpq
  have hflat : g.Flat := by
    exact RingHom.Flat.localRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
      q.asIdeal p.asIdeal hpq
  let : Algebra (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := g.toAlgebra
  let : Module.Flat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hflat
  let : IsNoetherianRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.isNoetherianRing q.asIdeal.primeCompl _ inferInstance
  let : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    change IsLocalHom g
    exact Localization.isLocalHom_localRingHom
      (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq
  let : Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := by
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap B (Localization.AtPrime q.asIdeal) (f x) =
        g (algebraMap A (Localization.AtPrime p.asIdeal) x)
      exact (Localization.localRingHom_to_map p.asIdeal q.asIdeal f hpq x).symm
    let : Algebra.FormallyUnramified A B := hf.formallyUnramified
    let : Algebra.FormallyUnramified B (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.of_isLocalization q.asIdeal.primeCompl
    let : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.comp A B (Localization.AtPrime q.asIdeal)
    exact Algebra.FormallyUnramified.localization_base p.asIdeal.primeCompl
  have hfess : Algebra.EssFiniteType A B := by
    change @Algebra.EssFiniteType A B _ _ f.toAlgebra
    let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
    infer_instance
  have hlocess : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := by
    exact Algebra.EssFiniteType.of_isLocalization
      (R := B) (S := Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl
  have hcomp :
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).EssFiniteType := by
    have heq : g.comp (algebraMap A (Localization.AtPrime p.asIdeal)) =
        (algebraMap B (Localization.AtPrime q.asIdeal)).comp f := by
      ext x
      simp [g]
    change @Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) _ _
      ((g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra)
    rw [heq]
    let : Algebra A B := f.toAlgebra
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      ((algebraMap B (Localization.AtPrime q.asIdeal)).comp f).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A B (Localization.AtPrime q.asIdeal) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A B := hfess
    let : Algebra.EssFiniteType B (Localization.AtPrime q.asIdeal) := hlocess
    exact Algebra.EssFiniteType.comp A B (Localization.AtPrime q.asIdeal)
  have hgess : g.EssFiniteType := by
    change @Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) _ _ g.toAlgebra
    let : Algebra (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := g.toAlgebra
    let : Algebra A (Localization.AtPrime p.asIdeal) :=
      (algebraMap A (Localization.AtPrime p.asIdeal)).toAlgebra
    let : SMul A (Localization.AtPrime p.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime p.asIdeal)).toSMul
    let : Algebra A (Localization.AtPrime q.asIdeal) :=
      (g.comp (algebraMap A (Localization.AtPrime p.asIdeal))).toAlgebra
    let : SMul A (Localization.AtPrime q.asIdeal) :=
      (inferInstance : Algebra A (Localization.AtPrime q.asIdeal)).toSMul
    let : IsScalarTower A (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal) := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra.EssFiniteType A (Localization.AtPrime q.asIdeal) := hcomp
    exact Algebra.EssFiniteType.of_comp A (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)
  let : Algebra.EssFiniteType (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) := hgess
  let R := Localization.AtPrime p.asIdeal
  let S := Localization.AtPrime q.asIdeal
  let : IsDedekindDomain R := IsLocalization.AtPrime.isDedekindDomain A p.asIdeal _
  have hmax : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S := by
    exact Algebra.FormallyUnramified.map_maximalIdeal
  by_cases hfield : IsField R
  · let : Field R := hfield.toField
    have hmaxS : IsLocalRing.maximalIdeal S = ⊥ := by
      rw [← hmax, IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
    let hfieldS : IsField S := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaxS
    let : IsField S := hfieldS
    let : Field S := hfieldS.toField
    let : IsDomain S := hfieldS.isDomain
    have hprincipal : IsPrincipalIdealRing S := inferInstance
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 0 2).mp
      hprincipal
  · have hmaxR : (IsLocalRing.maximalIdeal R).IsPrincipal :=
      maximalIdeal_isPrincipal_of_isDedekindDomain R
    obtain ⟨x, hx⟩ := hmaxR
    have hx0 : x ≠ 0 := by
      intro hx0
      apply (IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hfield)
      rw [hx, hx0]
      simp
    have hdomainR : IsDomain R := IsDedekindDomain.toIsDomain
    let : IsDomain R := hdomainR
    have hxR : x ∈ nonZeroDivisors R := by
      simpa using hx0
    have hxs : IsSMulRegular S (algebraMap R S x) := by
      have hxsR : IsSMulRegular S x :=
        Module.Flat.isSMulRegular_of_nonZeroDivisors hxR
      intro a b hab
      apply hxsR
      simpa [Algebra.smul_def] using hab
    have hdomain : IsDomain S := by
      apply isDomain_of_isLocalRing_of_isNoetherianRing_of_isSMulRegular
        (algebraMap R S x) hxs
      rw [← hmax, hx, Ideal.map_span]
      simp only [Set.image_singleton]
    let : IsDomain S := hdomain
    have hmaxS : (IsLocalRing.maximalIdeal S).IsPrincipal := by
      refine ⟨algebraMap R S x, ?_⟩
      rw [← hmax, hx, Ideal.map_span]
      simp only [Set.image_singleton]
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain S).out 4 2).mp hmaxS

private theorem ringKrullDim_le_one_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A] :
    ringKrullDim B ≤ 1 := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
  let : Algebra.QuasiFinite A B := inferInstance
  have hstrict : StrictMono (PrimeSpectrum.comap (algebraMap A B)) := by
    intro x y hxy
    have hle : x.asIdeal ≤ y.asIdeal := hxy.le
    have hcomap :
        (x.comap (algebraMap A B)).asIdeal ≤
          (y.comap (algebraMap A B)).asIdeal := by
      exact Ideal.comap_mono hle
    have hle' : x.comap (algebraMap A B) ≤ y.comap (algebraMap A B) := hcomap
    refine lt_of_le_of_ne hle' ?_
    intro heq
    apply hxy.ne
    apply PrimeSpectrum.ext
    apply Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := A) (S := B) x.asIdeal y.asIdeal hle
    simpa [Ideal.under_def] using congrArg PrimeSpectrum.asIdeal heq
  have hdimA : ringKrullDim A ≤ 1 := by
    exact Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  calc
    ringKrullDim B = Order.krullDim (PrimeSpectrum B) := rfl
    _ ≤ Order.krullDim (PrimeSpectrum A) :=
      Order.krullDim_le_of_strictMono _ hstrict
    _ = ringKrullDim A := rfl
    _ ≤ 1 := hdimA

/-- An étale extension of a Dedekind domain is a finite product of Dedekind
domains. -/
theorem isFiniteProductOfDedekindDomains_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A] :
    IsFiniteProductOfDedekindDomains B := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
  let : Algebra.EssFiniteType A B := inferInstance
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  have hnormal : Formalization.Books.Algebra.Unit37.IsNormalRing B := by
    intro q
    have hq : IsDedekindDomain (Localization.AtPrime q.asIdeal) :=
      isDedekindDomain_localization_atPrime_of_etale f hf q
    let : IsDedekindDomain (Localization.AtPrime q.asIdeal) := hq
    exact ⟨inferInstance, inferInstance⟩
  have hred : IsReduced B :=
    Formalization.Books.Algebra.Unit37.normalRing_isReduced hnormal
  let : IsReduced B := hred
  have hfinite : (minimalPrimes B).Finite :=
    minimalPrimes.finite_of_isNoetherianRing B
  have hprod : Formalization.Books.Algebra.Unit37.IsFiniteProductOfNormalDomains B :=
    ((Formalization.Books.Algebra.Unit37.normalRing_reduced_finite_minimalPrimes_TFAE
      hfinite).out 0 2).mp hnormal
  have hdimB : ringKrullDim B ≤ 1 := ringKrullDim_le_one_of_etale f hf
  rcases hprod with ⟨ι, hι, S, hS, hE⟩
  let : Fintype ι := hι
  obtain ⟨E⟩ := hE
  refine ⟨ι, hι, S, ?_, ⟨E⟩⟩
  intro i
  have hdomain : IsDomain (S i : Type v) := (hS i).1
  let : IsDomain (S i : Type v) := hdomain
  let ev : (∀ j, (S j : Type v)) →+* (S i : Type v) :=
    Pi.evalRingHom (fun j => (S j : Type v)) i
  let : IsNoetherianRing (∀ j, (S j : Type v)) :=
    isNoetherianRing_of_ringEquiv B E
  let : IsNoetherianRing (S i : Type v) :=
    isNoetherianRing_of_surjective (∀ j, (S j : Type v))
      (S i : Type v) ev (Function.surjective_eval _)
  have hdimProd : ringKrullDim (∀ j, (S j : Type v)) ≤ 1 := by
    rw [← E.ringKrullDim]
    exact hdimB
  have hdimFactor : ringKrullDim (S i : Type v) ≤ 1 := by
    calc
      ringKrullDim (S i : Type v) ≤ ringKrullDim (∀ j, (S j : Type v)) :=
        ringKrullDim_le_of_surjective ev (Function.surjective_eval _)
      _ ≤ 1 := hdimProd
  let : Ring.KrullDimLE 1 (S i : Type v) := Ring.krullDimLE_iff.mpr hdimFactor
  have hdimle : Ring.DimensionLEOne (S i : Type v) := by
    refine ⟨fun {P} hP hPprime => ?_⟩
    exact hPprime.isMaximal_of_ne_bot hP
  have hdedRing : IsDedekindRing (S i : Type v) := by
    apply (isDedekindRing_iff (A := (S i : Type v))
      (FractionRing (S i : Type v))).mpr
    refine ⟨inferInstance, hdimle, ?_⟩
    intro x hx
    exact (isIntegrallyClosed_iff (FractionRing (S i : Type v))).mp (hS i).2 hx
  let : IsDedekindRing (S i : Type v) := hdedRing
  infer_instance

private theorem not_isField_localization_atPrime_of_etale
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : RingHom.Etale f) [IsDedekindDomain A]
    (q : PrimeSpectrum B) (hq : q.asIdeal.comap f ≠ ⊥) :
    ¬ IsField (Localization.AtPrime q.asIdeal) := by
  let p : PrimeSpectrum A := q.comap f
  have hpq : p.asIdeal = q.asIdeal.comap f := rfl
  let : Algebra A B := f.toAlgebra
  let g := Localization.localRingHom p.asIdeal q.asIdeal f hpq
  have hflat : g.Flat := by
    exact RingHom.Flat.localRingHom
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
      q.asIdeal p.asIdeal hpq
  let R := Localization.AtPrime p.asIdeal
  let S := Localization.AtPrime q.asIdeal
  let : Algebra R S := g.toAlgebra
  let : Module.Flat R S := hflat
  let : IsLocalHom (algebraMap R S) := by
    change IsLocalHom g
    exact Localization.isLocalHom_localRingHom
      (I := p.asIdeal) (R := A) (P := B) q.asIdeal f hpq
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hnotfieldR : ¬ IsField R :=
    IsLocalization.AtPrime.not_isField A (P := p.asIdeal) (by simpa [p] using hq)
      (Localization.AtPrime p.asIdeal)
  intro hfieldS
  let : Field S := hfieldS.toField
  have hmaxS : IsLocalRing.maximalIdeal S = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
  have hmap : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal S :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 0 2).mp
      (inferInstance : IsLocalHom (algebraMap R S))
  have hmapbot : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) = ⊥ := by
    apply le_antisymm
    · rw [hmaxS] at hmap
      exact hmap
    · exact bot_le
  have hmaxR : IsLocalRing.maximalIdeal R = ⊥ := by
    apply Ideal.map_injective_of_faithfullyFlat (A := R) (B := S)
    rw [hmapbot, Ideal.map_bot]
  exact hnotfieldR (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaxR)

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
  intro q hq
  let : Algebra A B := f.toAlgebra
  let : Algebra.Etale A B := RingHom.Etale.toAlgebra hf
  let : Algebra.EssFiniteType A B := inferInstance
  let : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing A B
  let q' : PrimeSpectrum B := ⟨q.asIdeal, q.isMaximal.isPrime⟩
  have hq' : q'.asIdeal.comap f ≠ ⊥ := by
    simpa [q'] using hq
  have hnotfield : ¬ IsField (Localization.AtPrime q.asIdeal) := by
    simpa [q'] using not_isField_localization_atPrime_of_etale f hf q' hq'
  have hded : IsDedekindDomain (Localization.AtPrime q.asIdeal) :=
    isDedekindDomain_localization_atPrime_of_etale f hf q'
  let : IsDedekindDomain (Localization.AtPrime q.asIdeal) := hded
  have hdomain : IsDomain (Localization.AtPrime q.asIdeal) :=
    IsDedekindDomain.toIsDomain
  let : IsDomain (Localization.AtPrime q.asIdeal) := hdomain
  exact ⟨hdomain,
    ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q.asIdeal) hnotfield).out 0 2).mpr
      hded⟩

end Formalization.Books.MoreAlgebra.Unit44
