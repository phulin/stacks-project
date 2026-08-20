import Formalization.Books.Algebra.Unit50.ValuationRings
import Formalization.Books.Algebra.Unit54.EssentiallyFiniteType
import Formalization.Books.Algebra.Unit99.CriteriaForFlatness
import Formalization.Books.Algebra.Unit103.CohenMacaulayModules
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Commutative Algebra, Chapter 119: Around Krull-Akizuki

The source section is formalized with Mathlib's canonical local-ring,
Noetherian, dimension, valuation-ring, length, residue-field, localization,
finite-type, and completion interfaces.  The theorem proofs are deferred to
the proving stage; the concrete algebraic constructions below have their
source-faithful bodies.
-/

namespace Formalization.Books.Algebra.Unit119

open Set

universe u v

noncomputable section

/-! ## Domination and the local alternatives -/

/- The kernel and cokernel condition in the Kollár alternative is the common
   source-facing form of ``annihilated by a power of the maximal ideal''.  The
   cokernel is the quotient by the canonical `R`-linear map underlying `f`. -/
def IsFiniteLocalModification
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    (f : R →+* S) : Prop :=
  RingHom.Finite f ∧ ¬ Function.Bijective f ∧
    ∃ n m : ℕ,
      Formalization.Books.Algebra.Unit99.IsAnnihilatedByIdealPower
        (N := RingHom.ker f)
        (IsLocalRing.maximalIdeal R) n ∧
        (letI : Algebra R S := f.toAlgebra
         Formalization.Books.Algebra.Unit99.IsAnnihilatedByIdealPower
           (N := S ⧸ LinearMap.range (Algebra.linearMap R S))
           (IsLocalRing.maximalIdeal R) m)

/- The four alternatives are packaged as a finite family so that `∃!` records
   the source's phrase “exactly one”, rather than merely listing equivalent
   conditions. -/
def kollarAlternative
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (i : Fin 4) : Prop :=
  match i.1 with
  | 0 => IsArtinianRing R
  | 1 => IsRegularLocalRing R ∧ ringKrullDim R = 1
  | 2 => 2 ≤ Formalization.Books.Algebra.Unit72.localDepth R R
  | _ =>
      ∃ (S : CommRingCat.{u}) (f : CommRingCat.of R ⟶ S),
        IsFiniteLocalModification f.hom ∧
          (letI : Algebra R (S : Type u) := f.hom.toAlgebra
           ¬ IsLocalRing.maximalIdeal R ∈
              _root_.associatedPrimes R (S : Type u)) ∧
          Nontrivial (S : Type u)

theorem dominate_by_dimension_one
    {R K : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hfield : ¬ IsField R) :
    ∃ S : Subalgebra R K,
      IsLocalRing S ∧
        IsNoetherianRing S ∧
          ringKrullDim S = 1 ∧
              IsLocalHom (algebraMap R S) ∧
              RingHom.EssFiniteType (algebraMap R S) := by
  classical
  let m : Ideal R := IsLocalRing.maximalIdeal R
  have hm_ne_bot : m ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal R) hfield
  have hfg : m.FG := m.fg_of_isNoetherianRing
  let G : Set R := m.generators \ {0}
  have hGfinite : G.Finite := by
    change (m.generators \ ({0} : Set R)).Finite
    exact Set.Finite.sdiff (Submodule.FG.finite_generators hfg)
  have hGnonempty : G.Nonempty := by
    by_contra hG
    have hGempty : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hG
    have hgens : m.generators ⊆ ({0} : Set R) := by
      intro y hy
      by_contra hy0
      have : y ∈ G := ⟨hy, hy0⟩
      rw [hGempty] at this
      exact this
    have hm_le_bot : m ≤ (⊥ : Ideal R) := by
      rw [← m.span_generators]
      apply Ideal.span_le.2
      intro y hy
      have hy0 : y = 0 := hgens hy
      simp [hy0]
    exact hm_ne_bot (bot_unique hm_le_bot)
  let V0 : LocalSubring K := LocalSubring.range (algebraMap R K)
  obtain ⟨V, hVdom⟩ :=
    Formalization.Books.Algebra.Unit50.exists_valuationSubring_dominating V0
  obtain ⟨hVsub, hVlocal⟩ :=
    Formalization.Books.Algebra.Unit50.dominates_iff.mp hVdom
  have hRmem (r : R) : algebraMap R K r ∈ V.toSubring := by
    apply hVsub
    exact ⟨r, rfl⟩
  let F : Finset R := hGfinite.toFinset
  obtain ⟨x, hxF, hxmin⟩ :=
    Finset.exists_max_image F (fun z : R => V.valuation (algebraMap R K z))
      (by
        obtain ⟨z, hz⟩ := hGnonempty
        exact ⟨z, hGfinite.mem_toFinset.mpr hz⟩)
  have hxG : x ∈ G := hGfinite.mem_toFinset.mp hxF
  have hxmax : x ∈ m := by
    rw [← m.span_generators]
    exact Ideal.subset_span hxG.1
  have hx0 : x ≠ 0 := hxG.2
  have hxK : algebraMap R K x ≠ 0 := by
    intro hx
    apply hx0
    apply FaithfulSMul.algebraMap_injective R K
    simpa using hx
  have hxminG (y : R) (hy : y ∈ G) :
      V.valuation (algebraMap R K y) ≤ V.valuation (algebraMap R K x) :=
    hxmin y (hGfinite.mem_toFinset.mpr hy)
  let ratio : R → K := fun y => algebraMap R K y / algebraMap R K x
  have hratio (y : R) (hy : y ∈ G) : ratio y ∈ V.toSubring := by
    change ratio y ∈ V
    rw [← V.valuation_le_one_iff]
    dsimp [ratio]
    rw [V.valuation.map_div]
    exact div_le_one_of_le₀ (hxminG y hy) zero_le
  let A : Subalgebra R K := Algebra.adjoin R (ratio '' G)
  have hAfg : A.FG := by
    apply Subalgebra.fg_def.2
    exact ⟨ratio '' G, hGfinite.image ratio, rfl⟩
  let _ : IsNoetherianRing A := isNoetherianRing_of_fg hAfg
  have hAsubV : ∀ a : A, (a : K) ∈ V := by
    have hclosure : ∀ z : K, z ∈ A → z ∈ V := by
      intro z hz
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
          rcases hz with ⟨y, hy, rfl⟩
          exact hratio y hy
      | algebraMap r =>
          exact hRmem r
      | add x y hx hy ihx ihy =>
          exact V.add_mem _ _ ihx ihy
      | mul x y hx hy ihx ihy =>
          exact V.mul_mem _ _ ihx ihy
    intro a
    exact hclosure (a : K) a.property
  have hxA : algebraMap R A x ≠ 0 := by
    intro hx
    apply hxK
    simpa using congrArg (fun z : A => (z : K)) hx
  have hmap : Ideal.map (algebraMap R A) m =
      Ideal.span ({algebraMap R A x} : Set A) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap, ← m.span_generators]
      apply Ideal.span_le.2
      intro y hy
      show algebraMap R A y ∈ Ideal.span ({algebraMap R A x} : Set A)
      by_cases hy0 : y = 0
      · simp [hy0]
      · let z : A := ⟨ratio y, Algebra.subset_adjoin ⟨y, ⟨hy, hy0⟩, rfl⟩⟩
        have hzy : algebraMap R A y = algebraMap R A x * z := by
          apply Subtype.ext
          change algebraMap R K y = algebraMap R K x * ratio y
          dsimp [ratio]
          calc
            algebraMap R K y = algebraMap R K y * 1 := by rw [mul_one]
            _ = algebraMap R K y *
                (algebraMap R K x * (algebraMap R K x)⁻¹) := by
              rw [mul_inv_cancel₀ hxK]
            _ = algebraMap R K x *
                (algebraMap R K y * (algebraMap R K x)⁻¹) := by
              ring
            _ = algebraMap R K x *
                (algebraMap R K y / algebraMap R K x) := by
              congr 1
              exact (div_eq_mul_inv _ _).symm
        rw [hzy]
        simpa [mul_comm] using
          (Ideal.span ({algebraMap R A x} : Set A)).mul_mem_left z
            (Ideal.subset_span (Set.mem_singleton _))
    · apply Ideal.span_le.2
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact Ideal.mem_map_of_mem (algebraMap R A) hxmax
  have hxnonunit : ¬ IsUnit (algebraMap R A x) := by
    intro hxu
    have hxuV : IsUnit
        (⟨(algebraMap R K x), hAsubV (algebraMap R A x)⟩ :
          V.toLocalSubring.toSubring) := by
      have hmapu := hxu.map
        ((A.val : A →+* K).codRestrict V.toLocalSubring.toSubring
          (fun a => hAsubV a))
      change IsUnit (((A.val : A →+* K).codRestrict V.toLocalSubring.toSubring
        (fun a => hAsubV a)) (algebraMap R A x))
      exact hmapu
    let g0 : R →+* V0.toSubring :=
      (algebraMap R K).codRestrict V0.toSubring (fun r => ⟨r, rfl⟩)
    have hg0surj : Function.Surjective g0 := by
      rintro ⟨z, ⟨r, hr⟩⟩
      refine ⟨r, ?_⟩
      apply Subtype.ext
      exact hr
    have hg0local : IsLocalHom g0 := IsLocalHom.of_surjective g0 hg0surj
    have hxuV0 : IsUnit (g0 x) := by
      let _ : IsLocalHom (Subring.inclusion hVsub) := hVlocal
      exact isUnit_of_map_unit (Subring.inclusion hVsub) (g0 x) (by
        change IsUnit (⟨algebraMap R K x, _⟩ : V.toLocalSubring.toSubring)
        exact hxuV)
    let _ : IsLocalHom g0 := hg0local
    have hxuR : IsUnit x := isUnit_of_map_unit g0 x hxuV0
    have hxnonunitR : x ∈ nonunits R :=
      (IsLocalRing.mem_maximalIdeal x).mp hxmax
    exact hxnonunitR hxuR
  have hspan_ne_top : Ideal.span ({algebraMap R A x} : Set A) ≠ ⊤ := by
    intro htop
    have hdiv : algebraMap R A x ∣ (1 : A) := by
      rw [← Ideal.mem_span_singleton]
      rw [htop]
      simp
    exact hxnonunit (isUnit_iff_dvd_one.mpr hdiv)
  obtain ⟨q, hq⟩ := Ideal.nonempty_minimalPrimes hspan_ne_top
  let _ : q.IsPrime := hq.isPrime
  have hq_ne_bot : q ≠ ⊥ := by
    intro hqbot
    have hxq : algebraMap R A x ∈ q :=
      hq.le (Ideal.subset_span (by simp))
    rw [hqbot] at hxq
    exact hxA (by simpa using hxq)
  have hqheight_le : q.height ≤ 1 :=
    Formalization.Books.Algebra.Unit60.height_le_one_of_minimal_over_singleton
      (R := A) (algebraMap R A x) hq
  have hqheight_ne : q.height ≠ 0 := by
    intro hqzero
    exact hq_ne_bot ((Ideal.height_eq_zero_iff_eq_bot).mp hqzero)
  have hqheight : q.height = 1 :=
    le_antisymm hqheight_le ((Order.one_le_iff_ne_zero).mpr hqheight_ne)
  let T := Localization.AtPrime q
  let _ : IsNoetherianRing T := inferInstance
  have hTdim : ringKrullDim T = 1 := by
    calc
      ringKrullDim T = q.height := IsLocalization.AtPrime.ringKrullDim_eq_height q T
      _ = 1 := by exact_mod_cast hqheight
  have hqmap : Ideal.map (algebraMap R A) m ≤ q := by
    rw [hmap]
    exact hq.le
  have hcomap_eq : q.comap (algebraMap R A) = m := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      exact Ideal.comap_ne_top (algebraMap R A) hq.isPrime.ne_top
    · exact (Ideal.map_le_iff_le_comap).mp hqmap
  have hlocalRT : IsLocalHom (algebraMap R T) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap R T)).out 3 0).mp
    intro r hr
    have hrq : algebraMap R A r ∈ q := by
      have : r ∈ q.comap (algebraMap R A) := by
        rw [hcomap_eq]
        exact hr
      exact this
    have hmem :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff T q (algebraMap R A r)).2 hrq
    change algebraMap R T r ∈ IsLocalRing.maximalIdeal T
    simpa only [IsScalarTower.algebraMap_apply R A T r] using hmem
  have hunit (s : q.primeCompl) : IsUnit (A.val (s : A)) := by
    rw [isUnit_iff_ne_zero]
    intro hs
    apply s.2
    have hs0 : (s : A) = 0 := by
      apply Subtype.ext
      exact hs
    rw [hs0]
    exact q.zero_mem
  let f : T →ₐ[R] K := IsLocalization.liftAlgHom (f := A.val) hunit
  have hf : Function.Injective f := by
    change Function.Injective f.toRingHom
    rw [IsLocalization.injective_iff_map_algebraMap_eq q.primeCompl]
    intro a b
    constructor
    · intro hab
      have := congrArg f hab
      simpa using this
    · intro hab
      have hab' : a = b := by
        apply Subtype.ext
        simpa [f] using hab
      simp [hab']
  let S : Subalgebra R K := f.range
  let e : T ≃ₐ[R] S := AlgEquiv.ofInjective f hf
  let _ : IsNoetherianRing S := AlgHom.isNoetherianRing_range f
  let _ : IsLocalRing S := by
    exact e.toRingEquiv.isLocalRing
  have hSdim : ringKrullDim S = 1 := by
    rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact hTdim
  have hlocalRS : IsLocalHom (algebraMap R S) := by
    have helocal : IsLocalHom e.toRingHom := by
      constructor
      intro a ha
      have := IsUnit.map e.symm.toRingHom ha
      simpa using this
    have he_apply (z : T) : e.toRingEquiv.toRingHom z = e z := rfl
    have hcomp : e.toRingHom.comp (algebraMap R T) = algebraMap R S := by
      ext r
      simpa only [RingHom.comp_apply, he_apply] using
        congrArg (fun z : S => (z : K)) (e.commutes r)
    rw [← hcomp]
    infer_instance
  let _ : Algebra.FiniteType R A := (Subalgebra.fg_iff_finiteType A).mp hAfg
  have hRA : RingHom.FiniteType (algebraMap R A) := by
    rw [RingHom.finiteType_algebraMap]
    infer_instance
  have hAT : RingHom.EssFiniteType (algebraMap A T) := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization (R := A) (S := T) q.primeCompl
  have hcompAT : (algebraMap A T).comp (algebraMap R A) = algebraMap R T := by
    ext r
    exact IsScalarTower.algebraMap_apply R A T r
  have hRT : RingHom.EssFiniteType (algebraMap R T) := by
    have h := RingHom.EssFiniteType.comp
      (RingHom.FiniteType.essFiniteType hRA) hAT
    rw [hcompAT] at h
    exact h
  have hefinite : RingHom.FiniteType e.toRingHom :=
    RingHom.FiniteType.of_surjective _ e.surjective
  have hST : RingHom.EssFiniteType (algebraMap R S) := by
    have hcomp := RingHom.EssFiniteType.comp hRT
      (RingHom.FiniteType.essFiniteType hefinite)
    have he_apply (z : T) : e.toRingEquiv.toRingHom z = e z := rfl
    have heq : e.toRingHom.comp (algebraMap R T) = algebraMap R S := by
      ext r
      simpa only [RingHom.comp_apply, he_apply] using
        congrArg (fun z : S => (z : K)) (e.commutes r)
    rw [heq] at hcomp
    exact hcomp
  exact ⟨S, inferInstance, inferInstance, hSdim, hlocalRS, hST⟩

theorem kollar_local_ring_alternative
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃! i : Fin 4, kollarAlternative R i := by
  sorry

theorem exists_finite_local_modification_of_nonregular_dimension_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (hcotangent : 1 < Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R)) :
    ∃ (S : CommRingCat.{u}) (f : CommRingCat.of R ⟶ S),
      IsFiniteLocalModification f.hom ∧
        (letI : Algebra R (S : Type u) := f.hom.toAlgebra
         ¬ IsLocalRing.maximalIdeal R ∈
            _root_.associatedPrimes R (S : Type u)) := by
  sorry

/-! ## The two examples and the resolution remark -/

abbrev nonreducedExamplePowerSeries (k : Type u) [Field k] :=
  MvPowerSeries (Fin 2) k

def nonreducedExampleRelation (k : Type u) [Field k] :
    Ideal (nonreducedExamplePowerSeries k) :=
  Ideal.span
    ({(MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2} :
      Set (nonreducedExamplePowerSeries k))

abbrev nonreducedExampleRing (k : Type u) [Field k] :=
  nonreducedExamplePowerSeries k ⧸ nonreducedExampleRelation k

def nonreducedExampleX (k : Type u) [Field k] : nonreducedExampleRing k :=
  Ideal.Quotient.mk (nonreducedExampleRelation k)
    (MvPowerSeries.X (0 : Fin 2))

def nonreducedExampleY (k : Type u) [Field k] : nonreducedExampleRing k :=
  Ideal.Quotient.mk (nonreducedExampleRelation k)
    (MvPowerSeries.X (1 : Fin 2))

abbrev nonreducedExampleTargetRing (k : Type u) [Field k] :=
  nonreducedExampleRing k

def nonreducedExampleTargetX (k : Type u) [Field k] :
    nonreducedExampleTargetRing k :=
  nonreducedExampleX k

def nonreducedExampleTargetZ (k : Type u) [Field k] :
    nonreducedExampleTargetRing k :=
  nonreducedExampleY k

/- The element adjoined after `n` repetitions is the source's `y/x^n`,
   expressed in the localization in which `x` is invertible. -/
noncomputable def nonreducedExampleAdjoinedElement
    (k : Type u) [Field k] (n : ℕ) :
    Localization.Away (nonreducedExampleX k) :=
  Localization.mk (nonreducedExampleY k)
    ⟨(nonreducedExampleX k) ^ n,
      (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩

noncomputable def nonreducedExampleIteratedAdjoin
    (k : Type u) [Field k] (n : ℕ) :
    Subalgebra (nonreducedExampleRing k)
      (Localization.Away (nonreducedExampleX k)) :=
  Algebra.adjoin (nonreducedExampleRing k)
    ({nonreducedExampleAdjoinedElement k n} :
      Set (Localization.Away (nonreducedExampleX k)))

theorem nonreduced_example_properties (k : Type u) [Field k] :
    ∃ hN : IsNoetherianRing (nonreducedExampleRing k),
      ∃ hL : IsLocalRing (nonreducedExampleRing k),
        letI : IsNoetherianRing (nonreducedExampleRing k) := hN
        letI : IsLocalRing (nonreducedExampleRing k) := hL
        Formalization.Books.Algebra.Unit103.IsCohenMacaulay
            (nonreducedExampleRing k) (nonreducedExampleRing k) ∧
            ringKrullDim (nonreducedExampleRing k) = 1 ∧
            ∃ f : nonreducedExampleRing k →+*
                nonreducedExampleTargetRing k,
              IsFiniteLocalModification f ∧
                Function.Injective f ∧
                  (letI : Algebra (nonreducedExampleRing k)
                      (nonreducedExampleTargetRing k) := f.toAlgebra
                   ¬ IsLocalRing.maximalIdeal (nonreducedExampleRing k) ∈
                      _root_.associatedPrimes (nonreducedExampleRing k)
                        (nonreducedExampleTargetRing k)) ∧
                    f (nonreducedExampleX k) =
                        nonreducedExampleTargetX k ∧
                      f (nonreducedExampleY k) =
                        nonreducedExampleTargetX k *
                          nonreducedExampleTargetZ k := by
  classical
  let I := nonreducedExampleRelation k
  have hI : I ≠ ⊤ := by
    intro h
    have hspan : Ideal.span
        ({((MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2)} :
          Set (nonreducedExamplePowerSeries k)) = ⊤ := by
      simpa [I, nonreducedExampleRelation] using h
    have hunit : IsUnit
        ((MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2) :=
      Ideal.span_singleton_eq_top.mp hspan
    have hzero : IsUnit (0 : k) := by
      rw [← MvPowerSeries.constantCoeff_X (1 : Fin 2)]
      simp [MvPowerSeries.isUnit_iff_constantCoeff] at hunit
    exact not_isUnit_zero hzero
  have hN : IsNoetherianRing (nonreducedExampleRing k) := by
    infer_instance
  have hL : IsLocalRing (nonreducedExampleRing k) := by
    let : Nontrivial (nonreducedExampleRing k) :=
      Ideal.Quotient.nontrivial_iff.mpr hI
    apply IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing (nonreducedExampleRing k) := hN
  let : IsLocalRing (nonreducedExampleRing k) := hL
  let a : Fin 2 → nonreducedExamplePowerSeries k :=
    ![MvPowerSeries.X (0 : Fin 2),
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)]
  have ha : MvPowerSeries.HasSubst a := by
    constructor
    · intro s
      fin_cases s <;> simp [a]
    · intro d
      exact Set.toFinite _
  let g : nonreducedExamplePowerSeries k →+*
      nonreducedExamplePowerSeries k :=
    (MvPowerSeries.substAlgHom ha).toRingHom
  let f₀ : nonreducedExamplePowerSeries k →+*
      nonreducedExampleRing k :=
    (Ideal.Quotient.mk I).comp g
  have hker : I ≤ RingHom.ker f₀ := by
    rw [show I = Ideal.span
        ({((MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2)} :
          Set (nonreducedExamplePowerSeries k)) by
      rfl]
    refine Ideal.span_le.2 ?_
    intro z hz
    have hz' : z = (MvPowerSeries.X (1 : Fin 2) :
        nonreducedExamplePowerSeries k) ^ 2 := by
      simpa using hz
    rw [hz']
    change f₀ ((MvPowerSeries.X (1 : Fin 2) :
      nonreducedExamplePowerSeries k) ^ 2) = 0
    change Ideal.Quotient.mk I
      (g ((MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2)) = 0
    rw [map_pow, show g (MvPowerSeries.X (1 : Fin 2)) =
      MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2) by
        change MvPowerSeries.substAlgHom ha (MvPowerSeries.X (1 : Fin 2)) = _
        rw [MvPowerSeries.substAlgHom_X]
        rfl]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hy : (MvPowerSeries.X (1 : Fin 2) :
        nonreducedExamplePowerSeries k) ^ 2 ∈ I := by
      exact Ideal.subset_span (by simp)
    have hp : (MvPowerSeries.X (0 : Fin 2) :
        nonreducedExamplePowerSeries k) ^ 2 *
          (MvPowerSeries.X (1 : Fin 2) : nonreducedExamplePowerSeries k) ^ 2 ∈ I :=
      I.mul_mem_left _ hy
    rw [mul_pow]
    exact hp
  have hker' : ∀ x, x ∈ I → f₀ x = 0 := by
    intro x hx
    exact hker hx
  let f : nonreducedExampleRing k →+*
      nonreducedExampleTargetRing k :=
    Ideal.Quotient.lift I f₀ hker'
  refine ⟨hN, hL, ?_⟩
  refine And.intro (by sorry) ?_
  refine And.intro (by sorry) ?_
  refine ⟨f, ?_⟩
  refine And.intro (by sorry) ?_
  refine And.intro (by sorry) ?_
  refine And.intro (by sorry) ?_
  refine And.intro ?_ ?_
  · change (Ideal.Quotient.lift I f₀ hker')
        (Ideal.Quotient.mk I (MvPowerSeries.X (0 : Fin 2))) =
      Ideal.Quotient.mk I (MvPowerSeries.X (0 : Fin 2))
    rw [Ideal.Quotient.lift_mk]
    change Ideal.Quotient.mk I
        (MvPowerSeries.substAlgHom ha (MvPowerSeries.X (0 : Fin 2))) = _
    rw [MvPowerSeries.substAlgHom_X]
    rfl
  · change (Ideal.Quotient.lift I f₀ hker')
        (Ideal.Quotient.mk I (MvPowerSeries.X (1 : Fin 2))) =
      Ideal.Quotient.mk I (MvPowerSeries.X (0 : Fin 2)) *
        Ideal.Quotient.mk I (MvPowerSeries.X (1 : Fin 2))
    rw [Ideal.Quotient.lift_mk]
    change Ideal.Quotient.mk I
        (MvPowerSeries.substAlgHom ha (MvPowerSeries.X (1 : Fin 2))) = _
    rw [MvPowerSeries.substAlgHom_X]
    rfl

def pPowerSubfield (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] : Subfield k :=
  (frobenius k p).fieldRange

def finiteDegreeOverPowers (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] (s : Set k) : Prop :=
  ∃ F : IntermediateField (pPowerSubfield k p) k,
    s ⊆ (F : Set k) ∧ Module.Finite (pPowerSubfield k p) F

def badDvrCoefficientCondition (k : Type u) (p : ℕ) [Field k]
    [Fact p.Prime] [CharP k p] (f : PowerSeries k) : Prop :=
  finiteDegreeOverPowers k p
    (Set.range (fun i : ℕ => PowerSeries.coeff i f))

/- The structure records the concrete set defining `A`, its DVR property, its
   completion, and the infinite purely inseparable fraction-field extension.
   The fraction-field assertions use the canonical map induced by the inclusion
   `A.subtype`, as in Chapter 113. -/
structure BadDvrExampleData (k : Type u) (p : ℕ) [Field k] [Fact p.Prime]
    [CharP k p] where
  A : Subring (PowerSeries k)
  carrier_spec : ∀ f : PowerSeries k,
    f ∈ A ↔ badDvrCoefficientCondition k p f
  isDomain : IsDomain (A : Type u)
  isDVR : @IsDiscreteValuationRing (A : Type u) _ isDomain
  maximalIdeal : Ideal (A : Type u)
  maximalIdeal_isMaximal : maximalIdeal.IsMaximal
  completion_equiv : Nonempty
    (AdicCompletion maximalIdeal (A : Type u) ≃+* PowerSeries k)
  fractionField_infinite :
    (letI : IsDomain (A : Type u) := isDomain
     letI : Algebra (FractionRing (A : Type u)) (FractionRing (PowerSeries k)) :=
       (Formalization.Books.Algebra.Unit113.fractionFieldMap
          A.subtype A.subtype_injective).toAlgebra
     ¬ Module.Finite (FractionRing (A : Type u)) (FractionRing (PowerSeries k)))
  fractionField_purelyInseparable :
    (letI : IsDomain (A : Type u) := isDomain
     letI : Algebra (FractionRing (A : Type u)) (FractionRing (PowerSeries k)) :=
       (Formalization.Books.Algebra.Unit113.fractionFieldMap
          A.subtype A.subtype_injective).toAlgebra
     IsPurelyInseparable (FractionRing (A : Type u))
       (FractionRing (PowerSeries k)))

theorem bad_dvr_characteristic_p_example
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (hinfinite : ¬ Module.Finite (pPowerSubfield k p) k) :
    Nonempty (BadDvrExampleData k p) := by
  sorry

noncomputable def badDvrAdjoin
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : BadDvrExampleData k p) (f : PowerSeries k) :
    Subalgebra (D.A : Type u) (PowerSeries k) :=
  letI : Algebra (D.A : Type u) (PowerSeries k) := D.A.subtype.toAlgebra
  Algebra.adjoin (D.A : Type u) ({f} : Set (PowerSeries k))

theorem bad_dvr_adjoin_properties
    {k : Type u} {p : ℕ} [Field k] [Fact p.Prime] [CharP k p]
    (D : BadDvrExampleData k p) (f : PowerSeries k)
    (hf : f ∉ D.A) :
    ∃ hN : IsNoetherianRing (badDvrAdjoin D f),
      ∃ hL : IsLocalRing (badDvrAdjoin D f),
        ∃ hD : IsDomain (badDvrAdjoin D f),
          letI : IsNoetherianRing (badDvrAdjoin D f) := hN
          letI : IsLocalRing (badDvrAdjoin D f) := hL
          letI : IsDomain (badDvrAdjoin D f) := hD
          ringKrullDim (badDvrAdjoin D f) = 1 ∧
            ¬ IsReduced
              (AdicCompletion (IsLocalRing.maximalIdeal (badDvrAdjoin D f))
                (badDvrAdjoin D f)) := by
  sorry

def IsOneDimensionalSemilocalNoetherianDomain
    (R : Type u) [CommRing R] : Prop :=
  IsDomain R ∧ IsNoetherianRing R ∧ ringKrullDim R = 1 ∧
    Finite (MaximalSpectrum R)

def IsRegularSemilocalRing (R : Type u) [CommRing R] : Prop :=
  ∀ m : MaximalSpectrum R,
    IsRegularLocalRing (Localization.AtPrime m.asIdeal)

def HasFiniteBirationalExtension
    (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∃ S : CommRingCat.{u}, ∃ f : CommRingCat.of R ⟶ S,
    IsOneDimensionalSemilocalNoetherianDomain (S : Type u) ∧
      ∃ hS : IsDomain (S : Type u),
        letI : IsDomain (S : Type u) := hS
        RingHom.Finite f.hom ∧ Function.Injective f.hom ∧
          ∃ e : FractionRing R ≃+* FractionRing (S : Type u),
            e.toRingHom.comp (algebraMap R (FractionRing R)) =
              (algebraMap (S : Type u) (FractionRing (S : Type u))).comp f.hom

def HasRegularFiniteBirationalModel
    (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∃ S : CommRingCat.{u}, ∃ f : CommRingCat.of R ⟶ S,
    IsOneDimensionalSemilocalNoetherianDomain (S : Type u) ∧
      IsRegularSemilocalRing (S : Type u) ∧
      ∃ hS : IsDomain (S : Type u),
        letI : IsDomain (S : Type u) := hS
        RingHom.Finite f.hom ∧ Function.Injective f.hom ∧
          ∃ e : FractionRing R ≃+* FractionRing (S : Type u),
            e.toRingHom.comp (algebraMap R (FractionRing R)) =
              (algebraMap (S : Type u) (FractionRing (S : Type u))).comp f.hom

def AllLocalCompletionsReduced
    (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ m : MaximalSpectrum R,
    IsReduced
      (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime m.asIdeal))
        (Localization.AtPrime m.asIdeal))

theorem resolution_step_of_nonregular_maximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1)
    (hsemilocal : Finite (MaximalSpectrum R))
    (m : MaximalSpectrum R)
    (hnonregular : ¬ IsRegularLocalRing (Localization.AtPrime m.asIdeal)) :
    HasFiniteBirationalExtension R := by
  sorry

theorem reduced_local_completions_give_regular_model
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hsemilocal : Finite (MaximalSpectrum R))
    (hcompletion : AllLocalCompletionsReduced R) :
    HasRegularFiniteBirationalModel R := by
  sorry

theorem exists_characteristic_zero_nonreduced_completion
    : ∃ R : CommRingCat.{u},
      CharZero (R : Type u) ∧
        IsNoetherianRing (R : Type u) ∧ IsLocalRing (R : Type u) ∧
          IsDomain (R : Type u) ∧ ringKrullDim (R : Type u) = 1 ∧
            ∃ m : Ideal (R : Type u),
              m.IsMaximal ∧ ¬ IsReduced (AdicCompletion m (R : Type u)) := by
  sorry

/-! ## Discrete valuation rings and uniformizers -/

def HasPrincipalNonzeroMaximalIdeal
    (A : Type u) [CommRing A] : Prop :=
  ∃ m : Ideal A, m.IsMaximal ∧
    ∃ π : A, π ≠ 0 ∧ m = Ideal.span ({π} : Set A)

theorem characterize_discrete_valuation_ring
    {A : Type u} [CommRing A] :
    List.TFAE
      [ (∃ hA : IsDomain A, @IsDiscreteValuationRing A _ hA),
        (∃ hA : IsDomain A,
          @ValuationRing A _ hA ∧ IsNoetherianRing A ∧ ¬ IsField A),
        IsRegularLocalRing A ∧ ringKrullDim A = 1,
        IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧
          HasPrincipalNonzeroMaximalIdeal A,
        IsNoetherianRing A ∧ IsLocalRing A ∧
          Formalization.Books.Algebra.Unit37.IsNormalDomain A ∧
            ringKrullDim A = 1 ] := by
  sorry

def IsUniformizer
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (π : A) : Prop :=
  Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A

theorem uniformizers_associated
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {π ρ : A}
    (hπ : IsUniformizer π) (hρ : IsUniformizer ρ) :
    Associated π ρ := by
  sorry

theorem dvr_unique_unit_mul_pow
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {π : A}
    (hπ : IsUniformizer π) :
    ∀ x : A, x ≠ 0 →
      ∃! q : A × ℕ, IsUnit q.1 ∧ x = q.1 * π ^ q.2 := by
  sorry

/-! ## Length bounds and residue fields -/

theorem finite_length_submodule_bound
    {R K : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 1) (r : ℕ)
    (M : Submodule R (Fin r → K)) (x : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span ({x} : Set R)) < ⊤ ∧
      Module.length R
          (Formalization.Books.Algebra.Unit63.quotientByElement R
            (M : Type u) x) ≤
        (r : ℕ∞) * Module.length R (R ⧸ Ideal.span ({x} : Set R)) := by
  sorry

theorem finite_residue_field_fibres
    {R S K L : Type u} [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra K L] [Module.Finite K L]
    (f : R →+* S)
    (hcompat : (algebraMap K L).comp (algebraMap R K) =
      (algebraMap S L).comp f)
    (hinjective : Function.Injective (algebraMap K L))
    (hdim : ringKrullDim R = 1) :
    (∀ n : Ideal S, n.IsPrime →
      n.comap f = IsLocalRing.maximalIdeal R → n.IsMaximal) ∧
      Set.Finite
        {n : Ideal S | n.IsPrime ∧
          n.comap f = IsLocalRing.maximalIdeal R} ∧
        (∀ n : Ideal S, (hn : n.IsPrime) →
          n.comap f = IsLocalRing.maximalIdeal R →
            letI : n.IsPrime := hn
            ∃ φ : IsLocalRing.ResidueField R →+* n.ResidueField,
              (∀ r : R,
                φ (algebraMap R (IsLocalRing.ResidueField R) r) =
                  algebraMap S n.ResidueField (f r)) ∧
                (letI : Algebra (IsLocalRing.ResidueField R)
                    n.ResidueField := φ.toAlgebra
                 Module.Finite (IsLocalRing.ResidueField R)
                   n.ResidueField)) := by
  sorry

theorem finite_length_global_submodule
    {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hdim : ringKrullDim R = 1) (r : ℕ)
    (M : Submodule R (Fin r → K)) (x : R) (hx : x ≠ 0) :
    Module.length R
        (Formalization.Books.Algebra.Unit63.quotientByElement R
          (M : Type u) x) < ⊤ := by
  sorry

/-! ## Krull-Akizuki and dominating DVRs -/

theorem krull_akizuki
    {R K L : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L]
    (hdim : ringKrullDim R = 1) (A : Subalgebra R L) :
    IsNoetherianRing A := by
  sorry

/- The integral closure in a finite field extension is the standard
   Dedekind-domain consequence of Krull--Akizuki.  The explicit dimension
   instance is built from the supplied equality because Mathlib's integral-
   closure dimension theorem consumes `Ring.DimensionLEOne`. -/
theorem integral_closure_is_dedekind
    {R K L : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Module.Finite K L]
    (hdim : ringKrullDim R = 1) :
    IsDedekindDomain (integralClosure R L) := by
  letI : Ring.KrullDimLE 1 R :=
    Ring.krullDimLE_iff.mpr (by simpa [hdim])
  letI : Ring.DimensionLEOne R :=
    { maximalOfPrime := by
        intro p hp0 hp
        exact
          (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
            (inferInstance : Ring.KrullDimLE 1 R)) p hp0 hp }
  letI : IsNoetherianRing (integralClosure R L) :=
    krull_akizuki (R := R) (K := K) (L := L) hdim (integralClosure R L)
  letI : Ring.DimensionLEOne (integralClosure R L) :=
    Ring.DimensionLEOne.integralClosure R L
  letI : IsFractionRing (integralClosure R L) L :=
    integralClosure.isFractionRing_of_finite_extension (A := R) K L
  letI : IsIntegrallyClosed (integralClosure R L) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := R) K
  exact (isDedekindDomain_iff (A := integralClosure R L) L).2
    ⟨inferInstance, inferInstance, inferInstance,
      fun {x} hx => IsIntegrallyClosedIn.algebraMap_eq_of_integral hx⟩

theorem exists_dvr_dominating
    {R K L : Type u} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [Algebra.FiniteType K L]
    (hfield : ¬ IsField R) :
    ∃ A : Subalgebra R L,
      (∃ hA : IsDomain (A : Type u),
        @IsDiscreteValuationRing (A : Type u) _ hA) ∧
        IsFractionRing (A : Type u) L ∧
          IsLocalHom (algebraMap R A) := by
  sorry

end

end Formalization.Books.Algebra.Unit119
