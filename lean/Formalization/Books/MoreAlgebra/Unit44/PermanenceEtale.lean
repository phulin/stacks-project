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
import Mathlib.RingTheory.Unramified.Dedekind

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

private theorem spanFinrank_maximalIdeal_eq_of_flat_of_formallyUnramified
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] [IsLocalHom (algebraMap R S)]
    [Algebra.EssFiniteType R S]
    [Algebra.FormallyUnramified R S] :
    (IsLocalRing.maximalIdeal R).spanFinrank =
      (IsLocalRing.maximalIdeal S).spanFinrank := by
  letI : Module.FaithfullyFlat R S :=
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
    letI : Fintype (Set.range j') := Fintype.ofFinite _
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
    letI : Algebra.FormallyUnramified A B := hf.formallyUnramified
    letI : Algebra.FormallyUnramified B (Localization.AtPrime q.asIdeal) :=
      Algebra.FormallyUnramified.of_isLocalization q.asIdeal.primeCompl
    letI : Algebra.FormallyUnramified A (Localization.AtPrime q.asIdeal) :=
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
    letI : IsRegularLocalRing (Localization.AtPrime p.asIdeal) := hreg
    letI : IsNoetherianRing (Localization.AtPrime p.asIdeal) := inferInstance
    letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) := hnoeth.mp inferInstance
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
    letI : IsRegularLocalRing (Localization.AtPrime q.asIdeal) := hreg
    letI : IsNoetherianRing (Localization.AtPrime q.asIdeal) := inferInstance
    letI : IsNoetherianRing (Localization.AtPrime p.asIdeal) := hnoeth.mpr inferInstance
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
