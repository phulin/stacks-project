import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ENat.BigOperators
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalProperties.Basic
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
  exact (letI := hM.module; letI := Ideal.Quotient.field m; by
    have hlen : Module.length R M = Module.length (R ⧸ m) M :=
      Module.length_eq_of_surjective (R := R ⧸ m) (S := R) (M := M) m.mkQ_surjective
    have hleft : Module.length R M = (Module.rank (R ⧸ m) M).toENat := by
      rw [hlen]
      exact Module.length_eq_rank (R ⧸ m) M
    refine ⟨hleft, ?_⟩
    rw [show Module.length R M < ⊤ ↔ Module.length (R ⧸ m) M < ⊤ by rw [hlen]]
    constructor
    · intro h
      have hfiniteQ : Module.Finite (R ⧸ m) M := finite_length_finite h
      have hfiniteRQuot : Module.Finite R (R ⧸ m) :=
        Module.Finite.of_surjective (Algebra.linearMap R (R ⧸ m)) m.mkQ_surjective
      exact @Module.Finite.trans R (R ⧸ m) M _ _ _ _ _ _ _ hfiniteRQuot hfiniteQ
    · intro h
      have hfiniteQ : Module.Finite (R ⧸ m) M :=
        @Module.Finite.of_restrictScalars_finite R (R ⧸ m) M _ _ _ _ _ _ _ h
      have hlenQ : Module.length (R ⧸ m) M = Module.finrank (R ⧸ m) M :=
        @Module.length_eq_finrank (R ⧸ m) M _ _ _ hfiniteQ
      rw [hlenQ]
      simp)

theorem length_localize
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submonoid R) :
    Module.length (Localization S) (LocalizedModule S M) ≤
      Module.length R M := by
  let gi := Submodule.localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)
  let e : Submodule (Localization S) (LocalizedModule S M) ↪o Submodule R M :=
    { toFun := fun N => Submodule.comap (LocalizedModule.mkLinearMap S M)
          (N.restrictScalars R)
      inj' := GaloisInsertion.u_injective gi
      map_rel_iff' := GaloisInsertion.u_le_u_iff gi }
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding e

theorem length_finite_of_fg_maximalIdeal
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (hm : m.IsMaximal) (hm_fg : m.FG) [Module.Finite R M]
    (n : ℕ) (hpow : m ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.length R M < ⊤ := by
  have aux : ∀ (N : Type _), ∀ [AddCommGroup N] [Module R N] [Module.Finite R N],
      ∀ k : ℕ, m ^ k • (⊤ : Submodule R N) = ⊥ → IsFiniteLength R N := by
    intro N _ _ _ k
    induction k generalizing N with
    | zero =>
        intro hN
        have htop : (⊤ : Submodule R N) = ⊥ := by simpa using hN
        have hsub : Subsingleton N :=
          ⟨fun x y => by
            have hx : x ∈ (⊥ : Submodule R N) := by
              rw [← htop]
              exact Submodule.mem_top
            have hy : y ∈ (⊥ : Submodule R N) := by
              rw [← htop]
              exact Submodule.mem_top
            simpa using hx.trans hy.symm⟩
        exact @IsFiniteLength.of_subsingleton R _ N _ _ hsub
    | succ k ih =>
        intro hN
        let P : Submodule R N := m • (⊤ : Submodule R N)
        have hPfg : P.FG :=
          Submodule.FG.smul hm_fg Module.Finite.fg_top
        have hPfin : Module.Finite R P := Module.Finite.of_fg hPfg
        have hPpow : m ^ k • (⊤ : Submodule R P) = ⊥ := by
          rw [eq_bot_iff]
          intro x hx
          have hxmap : (x : N) ∈
              (m ^ k • (⊤ : Submodule R P)).map P.subtype := by
            exact ⟨x, hx, rfl⟩
          have hmap : (m ^ k • (⊤ : Submodule R P)).map P.subtype = ⊥ := by
            rw [Submodule.map_smul'', Submodule.map_subtype_top]
            simpa [P, pow_succ, Submodule.mul_smul] using hN
          rw [hmap] at hxmap
          have hxzero : (x : N) = 0 := by simpa using hxmap
          exact Subtype.ext hxzero
        have hPfinlen : IsFiniteLength R P :=
          @ih P _ _ hPfin hPpow
        have hQfin : Module.Finite R (N ⧸ P) :=
          Module.Finite.of_surjective P.mkQ P.mkQ_surjective
        have hQtorsion : Module.IsTorsionBySet R (N ⧸ P) m := by
          simpa [P] using Module.isTorsionBySet_quotient_ideal_smul N m
        have hQlt : Module.length R (N ⧸ P) < ⊤ :=
          (@dimension_is_length R (N ⧸ P) _ _ _ m hm hQtorsion).2.mpr hQfin
        have hQfinlen : IsFiniteLength R (N ⧸ P) :=
          Module.length_ne_top_iff.mp (ne_of_lt hQlt)
        have hPnoeth := (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinlen).1
        have hPart := (isFiniteLength_iff_isNoetherian_isArtinian.mp hPfinlen).2
        have hQnoeth := (isFiniteLength_iff_isNoetherian_isArtinian.mp hQfinlen).1
        have hQart := (isFiniteLength_iff_isNoetherian_isArtinian.mp hQfinlen).2
        exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
          ⟨(isNoetherian_iff_submodule_quotient P).mpr ⟨hPnoeth, hQnoeth⟩,
            (isArtinian_iff_submodule_quotient P).mpr ⟨hPart, hQart⟩⟩
  have hfin : IsFiniteLength R M :=
    @aux M _ _ (inferInstance : Module.Finite R M) n hpow
  rw [lt_top_iff_ne_top]
  exact Module.length_ne_top_iff.mpr hfin

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
  classical
  have hst : s.head = ⊥ ∧ s.last = ⊤ := ⟨hs, ht⟩
  let m (i : Fin s.length) : Ideal R :=
    Classical.choose
      (isSimpleModule_iff_quot_maximal.mp
        ((covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)))
  refine ⟨m, ?_⟩
  intro i
  have hi := (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
  have hmax := Classical.choose_spec
    (isSimpleModule_iff_quot_maximal.mp hi)
  refine ⟨?_, ?_, ?_⟩
  · simpa using hi
  · simpa [m] using hmax.1
  · simpa [m] using hmax.2

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
  constructor
  · intro hne
    let _ : Subsingleton (LocalizedModule.AtPrime m (R ⧸ m')) := by
      rw [LocalizedModule.subsingleton_iff]
      intro x
      obtain ⟨a, ha, b, hb, hab⟩ :=
        (Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_of_isMaximal hne))
      have hbnot : b ∉ m := by
        intro hbm
        have htop : (1 : R) ∈ m := by
          rw [← hab]
          exact m.add_mem ha hbm
        exact (m.ne_top_iff_one.mp
          (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))) htop
      refine ⟨b, (Ideal.mem_primeCompl_iff.mpr hbnot), ?_⟩
      refine Submodule.Quotient.induction_on
        (p := (m' : Submodule R R)) x ?_
      intro y
      rw [← Submodule.Quotient.mk_smul]
      change Submodule.Quotient.mk (b • y) = Submodule.Quotient.mk (0 : R)
      apply (Submodule.Quotient.eq (p := (m' : Submodule R R))).2
      simpa [smul_eq_mul, mul_comm] using m'.mul_mem_left y hb
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · intro heq
    subst m'
    exact ⟨by
      rw [← Ideal.localized'_eq_map (S := Localization.AtPrime m)
        (p := m.primeCompl) m]
      exact (localizedQuotientEquiv m.primeCompl (m : Submodule R R)).symm⟩

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
  classical
  have hfactor_length (i : Fin s.length) :
      Module.length (Localization.AtPrime m₀)
        (LocalizedModule.AtPrime m₀
          (s (Fin.succ i) ⧸
            Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))) =
        if m i = m₀ then 1 else 0 := by
    obtain ⟨e⟩ := hfactor i
    let e' := LocalizedModule.map m₀.primeCompl e.toLinearMap
    have he' : Function.Bijective e' := ⟨
      LocalizedModule.map_injective m₀.primeCompl e.toLinearMap e.injective,
      LocalizedModule.map_surjective m₀.primeCompl e.toLinearMap e.surjective⟩
    let eloc : LocalizedModule.AtPrime m₀
          (s (Fin.succ i) ⧸
            Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
          ≃ₗ[Localization.AtPrime m₀]
          LocalizedModule.AtPrime m₀ (R ⧸ m i) :=
      LinearEquiv.ofBijective e' he'
    by_cases hi : m i = m₀
    · obtain ⟨e₀⟩ := (localized_residueField m₀ (m i)).2 hi.symm
      let _ : IsSimpleModule (Localization.AtPrime m₀)
            (Localization.AtPrime m₀ ⧸
              m₀.map (algebraMap R (Localization.AtPrime m₀))) := by
        apply (isSimpleModule_iff_quot_maximal).2
        exact ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
      calc
        Module.length (Localization.AtPrime m₀)
            (LocalizedModule.AtPrime m₀
              (s (Fin.succ i) ⧸
                Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))) =
            Module.length (Localization.AtPrime m₀)
              (LocalizedModule.AtPrime m₀ (R ⧸ m i)) := eloc.length_eq
        _ = Module.length (Localization.AtPrime m₀)
              (Localization.AtPrime m₀ ⧸
                m₀.map (algebraMap R (Localization.AtPrime m₀))) := e₀.length_eq
        _ = 1 := Module.length_eq_one _ _
        _ = if m i = m₀ then 1 else 0 := by simp [hi]
    · have hi' : m₀ ≠ m i := fun h => hi h.symm
      obtain ⟨e₀⟩ := (localized_residueField m₀ (m i)).1 hi'
      calc
        Module.length (Localization.AtPrime m₀)
            (LocalizedModule.AtPrime m₀
              (s (Fin.succ i) ⧸
                Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))) =
            Module.length (Localization.AtPrime m₀)
              (LocalizedModule.AtPrime m₀ (R ⧸ m i)) := eloc.length_eq
        _ = Module.length (Localization.AtPrime m₀)
              (⊥ : Submodule (Localization.AtPrime m₀)
                (Localization.AtPrime m₀)) := e₀.length_eq
        _ = 0 := Module.length_bot
        _ = if m i = m₀ then 1 else 0 := by simp [hi]
  let S := Localization.AtPrime m₀
  have hstep (i : Fin s.length) :
      Module.length S (LocalizedModule.AtPrime m₀ (s (Fin.succ i))) =
        Module.length S (LocalizedModule.AtPrime m₀ (s (Fin.castSucc i))) +
          Module.length S
            (LocalizedModule.AtPrime m₀
              (s (Fin.succ i) ⧸
                Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))) := by
    let N := Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))
    let f := LocalizedModule.map m₀.primeCompl
      (Submodule.inclusion (s.step i).le)
    let g := LocalizedModule.map m₀.primeCompl N.mkQ
    have hf : Function.Injective f := by
      exact LocalizedModule.map_injective m₀.primeCompl _
        (Submodule.inclusion_injective _)
    have hg : Function.Surjective g := by
      exact LocalizedModule.map_surjective m₀.primeCompl _
        (Submodule.mkQ_surjective N)
    have hex0 : Function.Exact (Submodule.inclusion (s.step i).le) N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    have hex : Function.Exact f g := by
      simpa [f, g, LocalizedModule.map, IsLocalizedModule.mapExtendScalars,
        LinearMap.extendScalarsOfIsLocalizationEquiv,
        LinearMap.extendScalarsOfIsLocalization] using
        (LocalizedModule.map_exact m₀.primeCompl
          (Submodule.inclusion (s.step i).le) N.mkQ hex0)
    exact Module.length_eq_add_of_exact f g hf hg hex
  let a : Fin s.length → ℕ∞ := fun i => if m i = m₀ then 1 else 0
  let emb (k : Fin (s.length + 1)) (i : Fin k) : Fin s.length :=
    ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
  have hprefix (k : Fin (s.length + 1)) :
      Module.length S (LocalizedModule.AtPrime m₀ (s k)) =
        ∑ i : Fin k, a (emb k i) := by
    induction k using Fin.induction with
    | zero =>
        rw [← RelSeries.head, hs]
        rw [Module.length_eq_zero]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        exact Fin.elim0 i
    | succ i hi =>
        rw [hstep i, hfactor_length i, hi]
        change
          (∑ j : Fin i.val, a (emb i.castSucc j)) +
              (if m i = m₀ then 1 else 0) =
            ∑ j : Fin (i.val + 1), a (emb (Fin.succ i) j)
        calc
          (∑ j : Fin i.val, a (emb i.castSucc j)) +
                (if m i = m₀ then 1 else 0) =
              (∑ j : Fin i.val,
                  a (emb (Fin.succ i) (Fin.castSucc j))) +
                a (emb (Fin.succ i) (Fin.last i.val)) := by
            apply congrArg₂ (fun x y => x + y)
            · apply Finset.sum_congr rfl
              intro j hj
              simp [emb]
            · simp [emb, a]
          _ = ∑ j : Fin (i.val + 1), a (emb (Fin.succ i) j) :=
            (Fin.sum_univ_castSucc
              (fun j : Fin (i.val + 1) => a (emb (Fin.succ i) j))).symm
  let etop' := LocalizedModule.map m₀.primeCompl
    (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M).toLinearMap
  have hetop' : Function.Bijective etop' := ⟨
    LocalizedModule.map_injective m₀.primeCompl _ (Submodule.topEquiv.injective),
    LocalizedModule.map_surjective m₀.primeCompl _ (Submodule.topEquiv.surjective)⟩
  let etop : LocalizedModule.AtPrime m₀ (⊤ : Submodule R M) ≃ₗ[S]
      LocalizedModule.AtPrime m₀ M := LinearEquiv.ofBijective etop' hetop'
  have hlast :
      Module.length S (LocalizedModule.AtPrime m₀ M) =
        ∑ i : Fin s.length, a i := by
    rw [← etop.length_eq]
    have htop : s (Fin.last s.length) = ⊤ := by
      rw [← RelSeries.last, ht]
    have h := hprefix (Fin.last s.length)
    rw [htop] at h
    simpa [emb, a] using h
  have hcard :
      (Nat.card {i : Fin s.length // m i = m₀} : ℕ∞) =
        ∑ i : Fin s.length, a i := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    symm
    simp [a]
  rw [hcard, ← hlast]

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
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite (MaximalSpectrum B)
  classical
  obtain ⟨s, hs, ht⟩ :=
    (isFiniteLength_iff_exists_compositionSeries.mp hM)
  have hstepA (i : Fin s.length) :
      Module.length A (s (Fin.succ i)) =
        Module.length A (s (Fin.castSucc i)) +
          Module.length A
            (s (Fin.succ i) ⧸
              Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))) := by
    let N := Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))
    let f := (Submodule.inclusion (s.step i).le).restrictScalars A
    let g := N.mkQ.restrictScalars A
    have hf : Function.Injective f := by
      exact Submodule.inclusion_injective (s.step i).le
    have hg : Function.Surjective g := by
      exact Submodule.mkQ_surjective N
    have hex0 : Function.Exact (Submodule.inclusion (s.step i).le) N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]
    have hex : Function.Exact f g := by
      simpa [f, g] using hex0
    exact Module.length_eq_add_of_exact f g hf hg hex
  let q (i : Fin s.length) : MaximalSpectrum B :=
    let hsimple :=
      (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
    ⟨Classical.choose
        (isSimpleModule_iff_quot_maximal.mp hsimple),
      (Classical.choose_spec
        (isSimpleModule_iff_quot_maximal.mp hsimple)).1⟩
  have _ (i : Fin s.length) : (q i).asIdeal.IsMaximal := (q i).isMaximal
  have hfactor (i : Fin s.length) :
      Nonempty
        ((s (Fin.succ i) ⧸
            Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i)))
          ≃ₗ[B] q i |>.asIdeal.ResidueField) := by
    let hsimple :=
      (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
    obtain ⟨e⟩ := (Classical.choose_spec
      (isSimpleModule_iff_quot_maximal.mp hsimple)).2
    let e₀ : (B ⧸ (q i).asIdeal) ≃ₗ[B] (q i).asIdeal.ResidueField :=
      (LinearEquiv.ofBijective
        (Algebra.linearMap (B ⧸ (q i).asIdeal) (q i).asIdeal.ResidueField)
        (q i).asIdeal.bijective_algebraMap_quotient_residueField).restrictScalars B
    exact ⟨e.trans e₀⟩
  have hfactorA (i : Fin s.length) :
      Module.length A
          (s (Fin.succ i) ⧸
            Submodule.comap (s (Fin.succ i)).subtype (s (Fin.castSucc i))) =
        Module.length A (q i).asIdeal.ResidueField := by
    obtain ⟨e⟩ := hfactor i
    exact (e.restrictScalars A).length_eq
  let b (i : Fin s.length) : ℕ∞ :=
    Module.length A (q i).asIdeal.ResidueField
  let emb (k : Fin (s.length + 1)) (i : Fin k) : Fin s.length :=
    ⟨i, i.isLt.trans_le (Nat.le_of_lt_succ k.isLt)⟩
  have hprefix (k : Fin (s.length + 1)) :
      Module.length A (s k) = ∑ i : Fin k, b (emb k i) := by
    induction k using Fin.induction with
    | zero =>
        rw [← RelSeries.head, hs]
        rw [Module.length_eq_zero]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        exact Fin.elim0 i
    | succ i hi =>
        rw [hstepA i, hfactorA i, hi]
        change
          (∑ j : Fin i.val, b (emb i.castSucc j)) + b i =
            ∑ j : Fin (i.val + 1), b (emb (Fin.succ i) j)
        calc
          (∑ j : Fin i.val, b (emb i.castSucc j)) + b i =
              (∑ j : Fin i.val,
                  b (emb (Fin.succ i) (Fin.castSucc j))) +
                b (emb (Fin.succ i) (Fin.last i.val)) := by
            apply congrArg₂ (fun x y => x + y)
            · apply Finset.sum_congr rfl
              intro j hj
              simp [emb]
            · simp [emb]
          _ = ∑ j : Fin (i.val + 1), b (emb (Fin.succ i) j) :=
            (Fin.sum_univ_castSucc
              (fun j : Fin (i.val + 1) => b (emb (Fin.succ i) j))).symm
  let etop :=
    (Submodule.topEquiv : (⊤ : Submodule B M) ≃ₗ[B] M).restrictScalars A
  have hlength :
      Module.length A M = ∑ i : Fin s.length, b i := by
    rw [← etop.length_eq]
    have htop : s (Fin.last s.length) = ⊤ := by
      rw [← RelSeries.last, ht]
    have h := hprefix (Fin.last s.length)
    rw [htop] at h
    simpa [emb] using h
  have hmult (r : MaximalSpectrum B) :
      (Nat.card {i : Fin s.length // q i = r} : ℕ∞) =
        Module.length (Localization.AtPrime r.asIdeal)
          (LocalizedModule.AtPrime r.asIdeal M) := by
    have hcard :
        (Nat.card {i : Fin s.length // (q i).asIdeal = r.asIdeal} : ℕ∞) =
          (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := by
      let e :
          {i : Fin s.length // (q i).asIdeal = r.asIdeal} ≃
            {i : Fin s.length // q i = r} :=
        { toFun := fun i =>
            ⟨i.1, by
              apply MaximalSpectrum.ext
              exact i.2⟩
          invFun := fun i =>
            ⟨i.1, by
              exact congrArg MaximalSpectrum.asIdeal i.2⟩
          left_inv := by intro i; rfl
          right_inv := by intro i; rfl }
      simpa only [Nat.card_eq_fintype_card] using
        congrArg (fun n : ℕ => (n : ℕ∞)) (Fintype.card_congr e)
    exact hcard.symm.trans
      (compositionSeries_localized_multiplicity s hs ht
        (fun i => (q i).asIdeal) (fun i => (q i).isMaximal)
        (fun i => by
          let hsimple :=
            (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)
          exact (Classical.choose_spec
            (isSimpleModule_iff_quot_maximal.mp hsimple)).2) r.asIdeal)
  have hfiber (r : MaximalSpectrum B) :
      ∑ i ∈ (Finset.univ.filter (fun i : Fin s.length => q i = r)),
          Module.length A (q i).asIdeal.ResidueField =
        Module.length A r.asIdeal.ResidueField *
          (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := by
    calc
      (∑ i ∈ (Finset.univ.filter (fun i : Fin s.length => q i = r)),
          Module.length A (q i).asIdeal.ResidueField) =
          ∑ i ∈ (Finset.univ.filter (fun i : Fin s.length => q i = r)),
            Module.length A r.asIdeal.ResidueField := by
              apply Finset.sum_congr rfl
              intro i hi
              exact congrArg
                (fun z : MaximalSpectrum B =>
                  Module.length A z.asIdeal.ResidueField)
                (Finset.mem_filter.mp hi).2
      _ = Module.length A r.asIdeal.ResidueField *
          (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := by
            simp [Nat.card_eq_fintype_card, Fintype.card_subtype, mul_comm]
  have hgroup :
      (∑ i : Fin s.length, b i) =
        ∑ r : MaximalSpectrum B,
          Module.length A r.asIdeal.ResidueField *
            (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := by
    change
      (∑ i : Fin s.length,
          Module.length A (q i).asIdeal.ResidueField) = _
    calc
      (∑ i : Fin s.length,
          Module.length A (q i).asIdeal.ResidueField) =
          ∑ i ∈ (Finset.univ.filter
            (fun i : Fin s.length =>
              q i ∈ (Finset.univ : Finset (MaximalSpectrum B)))),
            Module.length A (q i).asIdeal.ResidueField := by simp
      _ = ∑ r : MaximalSpectrum B,
            ∑ i ∈ (Finset.univ.filter (fun i : Fin s.length => q i = r)),
              Module.length A (q i).asIdeal.ResidueField := by
        simpa using
          (Finset.sum_fiberwise_eq_sum_filter
            (Finset.univ : Finset (Fin s.length))
            (Finset.univ : Finset (MaximalSpectrum B)) q
            (fun i => Module.length A (q i).asIdeal.ResidueField)
          ).symm
      _ = ∑ r : MaximalSpectrum B,
            Module.length A r.asIdeal.ResidueField *
              (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := by
        simp_rw [hfiber]
  have hlocal (r : MaximalSpectrum B) :
      IsLocalHom (algebraMap A r.asIdeal.ResidueField) := by
    constructor
    intro a ha
    by_contra hna
    have haM : a ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal a).2 hna
    have haq : algebraMap A B a ∈ r.asIdeal := by
      have : a ∈ r.asIdeal.comap (algebraMap A B) := by
        rw [h_over r]
        exact haM
      exact this
    have haz : algebraMap A r.asIdeal.ResidueField a = 0 := by
      rw [IsScalarTower.algebraMap_apply A B r.asIdeal.ResidueField]
      exact Ideal.algebraMap_residueField_eq_zero.mpr haq
    exact ha.ne_zero haz
  have hcoeff (r : MaximalSpectrum B) :
      Module.length A r.asIdeal.ResidueField < ⊤ := by
    have := hfinite r
    have := hlocal r
    have hres :
        Module.length (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField r.asIdeal.ResidueField) < ⊤ := by
      rw [Module.length_eq_finrank]
      exact ENat.natCast_lt_top _
    calc
      Module.length A r.asIdeal.ResidueField =
          Module.length r.asIdeal.ResidueField r.asIdeal.ResidueField *
            Module.length (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField r.asIdeal.ResidueField) :=
        IsLocalRing.length_restrictScalars A r.asIdeal.ResidueField
          r.asIdeal.ResidueField
      _ < ⊤ := by
        rw [Module.length_eq_one]
        rw [lt_top_iff_ne_top]
        simpa only [one_mul] using (ne_of_lt hres)
  have hMfinite : Module.length A M < ⊤ := by
    rw [hlength, hgroup]
    rw [ENat.sum_lt_top]
    intro r hr
    exact WithTop.mul_lt_top (hcoeff r) (ENat.natCast_lt_top _)
  constructor
  · calc
      Module.length A M = ∑ i : Fin s.length, b i := hlength
      _ = ∑ r : MaximalSpectrum B,
          Module.length A r.asIdeal.ResidueField *
            (Nat.card {i : Fin s.length // q i = r} : ℕ∞) := hgroup
      _ = ∑ r : MaximalSpectrum B,
          Module.length A r.asIdeal.ResidueField *
            Module.length (Localization.AtPrime r.asIdeal)
              (LocalizedModule.AtPrime r.asIdeal M) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hmult r]
  · exact hMfinite

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
  rw [length_pullback (A := A) (B := B) (M := M)]
  have hC0 :
      Module.length B (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) ≠ 0 := by
    simpa [← pos_iff_ne_zero, Module.length_pos_iff] using
      (IsLocalRing.map_maximalIdeal_lt_top (algebraMap A B)).ne
  constructor
  · intro hM
    exact WithTop.mul_lt_top hM hB
  · intro h
    by_contra hM
    have hMtop : Module.length A M = ⊤ :=
      le_antisymm le_top (le_of_not_gt hM)
    rw [hMtop, ENat.top_mul hC0] at h
    exact (lt_irrefl _ h)

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
