import Mathlib.Data.PNat.Notation
import Mathlib.Data.PNat.Interval
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.LocalProperties.Semilocal

/-!
# Examples, Chapter 16: A Noetherian ring of infinite dimension

The opening observation that a Noetherian local ring has finite Krull dimension
is already provided by Mathlib's `FiniteRingKrullDim` instance from
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.  This file formalizes the
Nagata construction that follows it.
-/

noncomputable section

universe u

open scoped BigOperators

private theorem mvPolynomial_idealOfVars_isPrime
    (R : Type u) [CommRing R] [IsDomain R] (σ : Type*) :
    (MvPolynomial.idealOfVars σ R).IsPrime := by
  classical
  let f : MvPolynomial σ R →+* R := MvPolynomial.constantCoeff
  have hker : RingHom.ker f = MvPolynomial.idealOfVars σ R := by
    apply le_antisymm
    · intro p hp
      rw [MvPolynomial.idealOfVars, ← Set.image_univ]
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hzero
      have hm0 : m = 0 := by
        ext n
        by_contra hn
        exact hzero ⟨n, Set.mem_univ _, hn⟩
      subst m
      have hp' : MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0 := by
        change MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0
        change f p = 0 at hp
        change MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0 at hp
        exact hp
      exact (Finsupp.mem_support_iff.mp hm) hp'
    · rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro _ ⟨n, rfl⟩
      simp [f]
  rw [← hker]
  exact RingHom.ker_isPrime f

private theorem mvPolynomial_idealOfVars_isMaximal
    (K : Type u) [Field K] (σ : Type*) :
    (MvPolynomial.idealOfVars σ K).IsMaximal := by
  classical
  let f : MvPolynomial σ K →+* K := MvPolynomial.constantCoeff
  have hf : Function.Surjective f := by
    intro x
    exact ⟨MvPolynomial.C x, by simp [f]⟩
  have hfield : IsField (MvPolynomial σ K ⧸ RingHom.ker f) :=
    (RingHom.quotientKerEquivOfSurjective hf).toMulEquiv.isField
      (Field.toIsField K)
  have hker : RingHom.ker f = MvPolynomial.idealOfVars σ K := by
    apply le_antisymm
    · intro p hp
      rw [MvPolynomial.idealOfVars, ← Set.image_univ]
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hzero
      have hm0 : m = 0 := by
        ext n
        by_contra hn
        exact hzero ⟨n, Set.mem_univ _, hn⟩
      subst m
      have hp' : MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0 := by
        change MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0
        change f p = 0 at hp
        change MvPolynomial.coeff (0 : σ →₀ ℕ) p = 0 at hp
        exact hp
      exact (Finsupp.mem_support_iff.mp hm) hp'
    · rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro _ ⟨n, rfl⟩
      simp [f]
  rw [← hker]
  exact Ideal.Quotient.maximal_of_isField _ hfield

private theorem mvPolynomial_idealOfVars_height
    (K : Type u) [Field K] :
    ∀ n : ℕ, (MvPolynomial.idealOfVars (Fin n) K).height = n := by
  intro n
  induction n with
  | zero => simp [MvPolynomial.idealOfVars]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let b : Ideal (MvPolynomial (Fin n) K) :=
        MvPolynomial.idealOfVars (Fin n) K
      let p : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        Ideal.map (e : MvPolynomial (Fin (n + 1)) K →+*
          Polynomial (MvPolynomial (Fin n) K))
          (MvPolynomial.idealOfVars (Fin (n + 1)) K)
      have hbmax : b.IsMaximal := by
        exact mvPolynomial_idealOfVars_isMaximal K (Fin n)
      have hpmax : p.IsMaximal := by
        letI : (MvPolynomial.idealOfVars (Fin (n + 1)) K).IsMaximal :=
          mvPolynomial_idealOfVars_isMaximal K (Fin (n + 1))
        change (Ideal.map (e : MvPolynomial (Fin (n + 1)) K →+*
          Polynomial (MvPolynomial (Fin n) K))
          (MvPolynomial.idealOfVars (Fin (n + 1)) K)).IsMaximal
        exact Ideal.map_isMaximal_of_equiv e
      have himage :
          (e : MvPolynomial (Fin (n + 1)) K →+*
            Polynomial (MvPolynomial (Fin n) K)) ''
              (Set.range (MvPolynomial.X : Fin (n + 1) → _)) =
            (Polynomial.C '' (Set.range (MvPolynomial.X : Fin n → _))) ∪
              {Polynomial.X} := by
        ext y
        constructor
        · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
          refine Fin.cases ?_ (fun j ↦ ?_) j
          · exact Or.inr (Set.mem_singleton_iff.mpr (by
              simpa [e] using (MvPolynomial.finSuccEquiv_X_zero (R := K) (n := n))))
          · exact Or.inl ⟨MvPolynomial.X j, ⟨j, rfl⟩,
              (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := n)).symm⟩
        · intro hy
          rcases hy with ⟨⟨x, ⟨j, rfl⟩, rfl⟩⟩ | rfl
          · exact ⟨MvPolynomial.X j.succ,
              ⟨j.succ, rfl⟩,
              (MvPolynomial.finSuccEquiv_X_succ (R := K) (n := n))⟩
          · exact ⟨MvPolynomial.X 0, ⟨0, rfl⟩,
              (MvPolynomial.finSuccEquiv_X_zero (R := K) (n := n))⟩
      have hp_eq :
          p = b.map Polynomial.C ⊔ Ideal.span {Polynomial.X} := by
        dsimp [p]
        rw [MvPolynomial.idealOfVars, Ideal.map_span, himage,
          Ideal.span_union]
        dsimp [b]
        rw [MvPolynomial.idealOfVars, Ideal.map_span]
      have hlies : p.LiesOver b := by
        refine ⟨?_⟩
        rw [hp_eq]
        apply le_antisymm
        ·
          exact Ideal.le_comap_map.trans (Ideal.comap_mono le_sup_left)
        · intro r hr
          change Polynomial.C r ∈ b.map Polynomial.C ⊔ Ideal.span {Polynomial.X} at hr
          rcases Submodule.mem_sup.mp hr with ⟨y, hy, z, hz, heq⟩
          have hy0 : y.coeff 0 ∈ b := (Ideal.mem_map_C_iff.mp hy) 0
          have hz0 : z.coeff 0 = 0 := by
            rw [Ideal.mem_span_singleton] at hz
            obtain ⟨w, rfl⟩ := hz
            simp
          have hcoeff : y.coeff 0 = r := by
            have hcoeff' := congrArg (fun q => q.coeff 0) heq
            simpa [hz0] using hcoeff'
          rw [← hcoeff]
          exact hy0
      letI : p.IsMaximal := hpmax
      letI : p.LiesOver b := hlies
      have hheight : p.height = b.height + 1 :=
        Polynomial.height_eq_height_add_one b p
      have heheight : p.height =
          (MvPolynomial.idealOfVars (Fin (n + 1)) K).height := by
        exact e.height_map _
      rw [← heheight, hheight, ih]
      norm_num

private instance mvPolynomial_idealOfVars_isPrime_inst
    (K : Type u) [Field K] (σ : Type*) :
    (MvPolynomial.idealOfVars σ K).IsPrime :=
  mvPolynomial_idealOfVars_isPrime K σ

private noncomputable def localization_atPrime_ringEquiv_of_map_eq
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S)
    [P.IsPrime] [Q.IsPrime] (h : Ideal.map e P = Q) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q := by
  classical
  have hcomap : Q.comap e = P := by
    ext x
    rw [Ideal.mem_comap, ← h, Ideal.apply_mem_of_equiv_iff]
  have hM : P.primeCompl.map e = Q.primeCompl := by
    ext x
    constructor
    · intro hx
      rcases (Submonoid.mem_map.mp hx) with ⟨y, hy, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hy ⊢
      intro hey
      apply hy
      have hy' : y ∈ Q.comap e := hey
      rw [hcomap] at hy'
      exact hy'
    · intro hx
      obtain ⟨y, rfl⟩ := e.surjective x
      apply Submonoid.mem_map.mpr
      refine ⟨y, ?_, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hx ⊢
      intro hy
      apply hx
      have hy' : e y ∈ Ideal.map e P := Ideal.mem_map_of_mem e hy
      rw [h] at hy'
      exact hy'
  exact IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime P) (Localization.AtPrime Q) e hM

private noncomputable def localization_atPrime_algEquiv_of_comap_eq
    {R : Type*} [CommSemiring R] (M : Submonoid R)
    (Q : Ideal (Localization M)) [Q.IsPrime]
    (P : Ideal R) [P.IsPrime]
    (h : Q.comap (algebraMap R (Localization M)) = P) :
    Localization.AtPrime P ≃ₐ[R] Localization.AtPrime Q := by
  let F : {p : Ideal R // p.IsPrime} → Type _ := fun p =>
    Localization (@Ideal.primeCompl R _ p.1 p.2)
  let pP : {p : Ideal R // p.IsPrime} := ⟨P, inferInstance⟩
  let pC : {p : Ideal R // p.IsPrime} :=
    ⟨Q.comap (algebraMap R (Localization M)), inferInstance⟩
  have hp : pP = pC := by
    apply Subtype.ext
    exact h.symm
  let c : F pP ≃ₐ[R] F pC := AlgEquiv.cast hp
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M Q
  change F pP ≃ₐ[R] Localization.AtPrime Q
  exact c.trans e

private theorem finiteMvPolynomial_idealOfVars_localization_properties
    (K : Type u) [Field K] (n : ℕ) :
    IsNoetherianRing
        (Localization.AtPrime (MvPolynomial.idealOfVars (Fin n) K)) ∧
      IsLocalRing (Localization.AtPrime (MvPolynomial.idealOfVars (Fin n) K)) ∧
      ringKrullDim (Localization.AtPrime (MvPolynomial.idealOfVars (Fin n) K)) =
        (↑n : WithBot ℕ∞) := by
  letI : (MvPolynomial.idealOfVars (Fin n) K).IsPrime :=
    mvPolynomial_idealOfVars_isPrime K (Fin n)
  have hdim :
      ringKrullDim (Localization.AtPrime (MvPolynomial.idealOfVars (Fin n) K)) =
        (↑n : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (MvPolynomial.idealOfVars (Fin n) K)]
    exact_mod_cast mvPolynomial_idealOfVars_height K n
  exact ⟨inferInstance, inferInstance, hdim⟩

private theorem finiteMvPolynomial_idealOfVars_localization_properties_finite
    (K : Type u) [Field K] (σ : Type*) [Finite σ] :
    IsNoetherianRing
        (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) ∧
      IsLocalRing (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) ∧
      ringKrullDim (Localization.AtPrime (MvPolynomial.idealOfVars σ K)) =
        (↑(Nat.card σ) : WithBot ℕ∞) := by
  classical
  letI := Fintype.ofFinite σ
  let e := MvPolynomial.renameEquiv K (Fintype.equivFin σ)
  let q := MvPolynomial.idealOfVars (Fin (Fintype.card σ)) K
  letI : q.IsPrime := mvPolynomial_idealOfVars_isPrime K _
  have hmap :
      Ideal.map e.toRingEquiv
          (MvPolynomial.idealOfVars σ K) = q := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    dsimp [q]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fintype.equivFin σ a, by simp [e]
      ⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a', rfl⟩ := (Fintype.equivFin σ).surjective a
      exact ⟨MvPolynomial.X a', ⟨a', rfl⟩, by simp [e]
      ⟩
  have hcomap :
      q.comap e.toRingEquiv =
        MvPolynomial.idealOfVars σ K := by
    ext x
    rw [Ideal.mem_comap, ← hmap, Ideal.apply_mem_of_equiv_iff]
  have hM :
      (MvPolynomial.idealOfVars σ K).primeCompl.map
          (e.toRingEquiv : MvPolynomial σ K ≃* MvPolynomial (Fin (Fintype.card σ)) K) =
        q.primeCompl := by
    ext x
    constructor
    · intro hx
      rcases (Submonoid.mem_map.mp hx) with ⟨y, hy, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hy ⊢
      intro hey
      apply hy
      have hy' : y ∈ q.comap e.toRingEquiv := hey
      rw [hcomap] at hy'
      exact hy'
    · intro hx
      obtain ⟨y, rfl⟩ := e.toRingEquiv.surjective x
      apply Submonoid.mem_map.mpr
      refine ⟨y, ?_, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hx ⊢
      intro hy
      apply hx
      have hy' : e y ∈ Ideal.map e.toRingEquiv (MvPolynomial.idealOfVars σ K) :=
        Ideal.mem_map_of_mem e.toRingEquiv hy
      rw [hmap] at hy'
      exact hy'
  let eloc :
      Localization.AtPrime (MvPolynomial.idealOfVars σ K) ≃+*
        Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (MvPolynomial.idealOfVars σ K))
      (Localization.AtPrime q) e.toRingEquiv hM
  have hq := finiteMvPolynomial_idealOfVars_localization_properties
    K (Fintype.card σ)
  letI := hq.1
  letI := hq.2.1
  refine ⟨isNoetherianRing_of_ringEquiv _ eloc.symm, ?_, ?_⟩
  · exact eloc.symm.isLocalRing
  · rw [ringKrullDim_eq_of_ringEquiv eloc]
    simpa [Nat.card_eq_fintype_card] using hq.2.2

namespace Formalization.Books.Examples.Unit16

/-- The opening observation: a Noetherian local ring has finite Krull dimension.

This is the canonical `FiniteRingKrullDim` instance supplied by Mathlib's
Noetherian local-ring theory.
-/
theorem noetherian_local_ring_has_finite_krull_dimension
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    FiniteRingKrullDim R :=
  inferInstance

/-- The countable polynomial ring `k[x₁, x₂, x₃, ...]`, indexed by positive
naturals as in the source. -/
abbrev NoetherianInfiniteDimensionPolynomialRing (k : Type u) [Field k] :=
  MvPolynomial ℕ+ k

/-- The variable `xₙ` in the countable polynomial ring. -/
def noetherianInfiniteDimensionVariable (k : Type u) [Field k] (n : ℕ+) :
    NoetherianInfiniteDimensionPolynomialRing k :=
  MvPolynomial.X n

/-- The block of indices from `2^(i - 1)` through `2^i - 1`.

The half-open interval is the canonical set-level representation of the
finite list of variables displayed in the source.
-/
def noetherianInfiniteDimensionBlock (i : ℕ+) : Set ℕ+ :=
  Set.Ico
    ⟨2 ^ ((i : ℕ) - 1), by positivity⟩
    ⟨2 ^ (i : ℕ), by positivity⟩

/-- The ideal generated by the variables in the `i`th block. -/
def noetherianInfiniteDimensionBlockIdeal (k : Type u) [Field k] (i : ℕ+) :
    Ideal (NoetherianInfiniteDimensionPolynomialRing k) :=
  Ideal.span
    (noetherianInfiniteDimensionVariable k '' noetherianInfiniteDimensionBlock i)

/-- Each block ideal is prime, as the source states. -/
instance noetherianInfiniteDimensionBlockIdeal_isPrime
    (k : Type u) [Field k] (i : ℕ+) :
    (noetherianInfiniteDimensionBlockIdeal k i).IsPrime := by
  classical
  let s : Set ℕ+ := noetherianInfiniteDimensionBlock i
  let f : {n : ℕ+ // n ∉ s} → ℕ+ := fun n => n.1
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (show x.1 = y.1 from hxy)
  let φ : MvPolynomial ℕ+ k →ₐ[k] MvPolynomial {n : ℕ+ // n ∉ s} k :=
    MvPolynomial.killCompl hf
  have hker : RingHom.ker φ.toRingHom =
    Ideal.span (MvPolynomial.X '' s : Set (MvPolynomial ℕ+ k)) := by
    apply le_antisymm
    · intro p hp
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hno
      push Not at hno
      have hsub : (m.support : Set ℕ+) ⊆ Set.range f := by
        intro n hn
        by_contra hnr
        have hns : n ∈ s := by
          by_contra hns
          exact hnr ⟨⟨n, hns⟩, rfl⟩
        exact (Finsupp.mem_support_iff.mp hn) (hno n hns)
      have hmap : Finsupp.mapDomain f
          (Finsupp.comapDomain f m hf.injOn) = m :=
        Finsupp.mapDomain_comapDomain f hf m hsub
      have hcoeff : p.coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
      have heq := congrArg (fun q : MvPolynomial {n : ℕ+ // n ∉ s} k =>
          q.coeff (Finsupp.comapDomain f m hf.injOn)) (RingHom.mem_ker.mp hp)
      change (MvPolynomial.killCompl hf p).coeff
          (Finsupp.comapDomain f m hf.injOn) = 0 at heq
      rw [MvPolynomial.coeff_killCompl, hmap] at heq
      exact hcoeff heq
    · rw [Ideal.span_le]
      rintro _ ⟨n, hn, rfl⟩
      change φ (MvPolynomial.X n) = 0
      simp only [φ, MvPolynomial.killCompl, MvPolynomial.aeval_X]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        have hmnot : f m ∉ s := by simpa [f] using m.property
        exact (hmnot hn).elim
      · rfl
  have hprime : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime φ.toRingHom
  simpa [noetherianInfiniteDimensionBlockIdeal,
    noetherianInfiniteDimensionVariable, s] using hker ▸ hprime

/-- The multiplicative set `⋂ᵢ (R \ 𝔭ᵢ)`, represented as a submonoid. -/
def noetherianInfiniteDimensionMultiplicativeSet (k : Type u) [Field k] :
    Submonoid (NoetherianInfiniteDimensionPolynomialRing k) :=
  ⨅ i : ℕ+, (noetherianInfiniteDimensionBlockIdeal k i).primeCompl

/-- The carrier of the chosen submonoid is the displayed intersection of
complements of the block ideals. -/
theorem noetherianInfiniteDimensionMultiplicativeSet_coe
    (k : Type u) [Field k] :
    (noetherianInfiniteDimensionMultiplicativeSet k :
      Set (NoetherianInfiniteDimensionPolynomialRing k)) =
      ⋂ i : ℕ+, (noetherianInfiniteDimensionBlockIdeal k i :
      Set (NoetherianInfiniteDimensionPolynomialRing k))ᶜ := by
  ext x
  simp [noetherianInfiniteDimensionMultiplicativeSet]

/-- The localization `A = S⁻¹R` in the source construction. -/
abbrev NoetherianInfiniteDimensionLocalization (k : Type u) [Field k] :=
  Localization (noetherianInfiniteDimensionMultiplicativeSet k)

/-- The extension `𝔪ᵢ = 𝔭ᵢ A` of a block ideal to `A`. -/
def noetherianInfiniteDimensionLocalizedBlockIdeal (k : Type u) [Field k]
    (i : ℕ+) : Ideal (NoetherianInfiniteDimensionLocalization k) :=
  Ideal.map (algebraMap (NoetherianInfiniteDimensionPolynomialRing k)
    (NoetherianInfiniteDimensionLocalization k))
    (noetherianInfiniteDimensionBlockIdeal k i)

/-- The ideals `𝔪ᵢ = 𝔭ᵢ A` are maximal ideals of `A`. -/
instance noetherianInfiniteDimensionLocalizedBlockIdeal_isMaximal
    (k : Type u) [Field k] (i : ℕ+) :
    (noetherianInfiniteDimensionLocalizedBlockIdeal k i).IsMaximal := by
  classical
  let n : ℕ+ := ⟨2 ^ ((i : ℕ) - 1), by positivity⟩
  have hpow : 2 ^ ((i : ℕ) - 1) < 2 ^ (i : ℕ) := by
    have hi : (i : ℕ) = ((i : ℕ) - 1) + 1 := (Nat.sub_add_cancel i.2).symm
    have hpos : 0 < 2 ^ ((i : ℕ) - 1) := by positivity
    calc
      2 ^ ((i : ℕ) - 1) < 2 ^ ((i : ℕ) - 1) * 2 := by nlinarith
      _ = 2 ^ (((i : ℕ) - 1) + 1) := (pow_succ 2 ((i : ℕ) - 1)).symm
      _ = 2 ^ (i : ℕ) := (congrArg (fun e : ℕ => 2 ^ e) hi).symm
  have hn : n ∈ noetherianInfiniteDimensionBlock i := by
    exact ⟨le_rfl, hpow⟩
  have hdisj : ∀ j : ℕ+, j ≠ i → n ∉ noetherianInfiniteDimensionBlock j := by
    intro j hji hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hpow' : 2 ^ (j : ℕ) ≤ 2 ^ ((i : ℕ) - 1) := by
        apply Nat.pow_le_pow_right (by omega)
        have hlt' : (j : ℕ) < (i : ℕ) := hlt
        omega
      change 2 ^ ((j : ℕ) - 1) ≤ n ∧ n < 2 ^ (j : ℕ) at hj
      exact (not_lt_of_ge hpow') hj.2
    · have hpow' : 2 ^ (i : ℕ) ≤ 2 ^ ((j : ℕ) - 1) := by
        apply Nat.pow_le_pow_right (by omega)
        have hgt' : (i : ℕ) < (j : ℕ) := hgt
        omega
      change 2 ^ ((j : ℕ) - 1) ≤ n ∧ n < 2 ^ (j : ℕ) at hj
      exact (not_le_of_gt hpow) (hpow'.trans hj.1)
  have havoid : ∀ p : NoetherianInfiniteDimensionPolynomialRing k,
      p ∉ noetherianInfiniteDimensionBlockIdeal k i →
        p + noetherianInfiniteDimensionVariable k n ^ (p.totalDegree + 1) ∈
          noetherianInfiniteDimensionMultiplicativeSet k := by
    intro p hp
    change p + noetherianInfiniteDimensionVariable k n ^ (p.totalDegree + 1) ∈
      (noetherianInfiniteDimensionMultiplicativeSet k : Set _)
    rw [noetherianInfiniteDimensionMultiplicativeSet_coe]
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro j hj
    have hjmem := hj
    change p + MvPolynomial.X n ^ (p.totalDegree + 1) ∈
      Ideal.span (MvPolynomial.X '' noetherianInfiniteDimensionBlock j) at hj
    rw [MvPolynomial.mem_ideal_span_X_image] at hj
    have hpc : p.coeff (Finsupp.single n (p.totalDegree + 1)) = 0 := by
      by_contra hpc
      have hd : Finsupp.single n (p.totalDegree + 1) ∈ p.support :=
        Finsupp.mem_support_iff.mpr hpc
      have hle := MvPolynomial.le_totalDegree hd
      have hle' : (Finsupp.single n p.totalDegree + Finsupp.single n 1).sum
          (fun _ e => e) ≤ p.totalDegree := by
        simpa only [Finsupp.single_add] using hle
      have hsum : (Finsupp.single n p.totalDegree + Finsupp.single n 1).sum
          (fun _ e => e) = p.totalDegree + 1 := by
        rw [Finsupp.sum_add_index']
        · rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
          all_goals rfl
        · intro _
          rfl
        · intro _ _ _
          rfl
      rw [hsum] at hle'
      omega
    have hqcoeff :
        (p + MvPolynomial.X n ^ (p.totalDegree + 1)).coeff
            (Finsupp.single n (p.totalDegree + 1)) = 1 := by
      rw [MvPolynomial.coeff_add, hpc, MvPolynomial.coeff_X_pow]
      simp
    have hdmem : Finsupp.single n (p.totalDegree + 1) ∈
        (p + MvPolynomial.X n ^ (p.totalDegree + 1)).support := by
      apply Finsupp.mem_support_iff.mpr
      change MvPolynomial.coeff (Finsupp.single n (p.totalDegree + 1))
        (p + MvPolynomial.X n ^ (p.totalDegree + 1)) ≠ 0
      rw [hqcoeff]
      exact one_ne_zero
    obtain ⟨x, hx, hxcoeff⟩ := hj _ hdmem
    have hxn : x = n := by
      by_contra hxn
      apply hxcoeff
      simp [hxn]
    subst x
    by_cases hji : j = i
    · subst j
      apply hp
      have hxnmem : MvPolynomial.X n ∈
          (MvPolynomial.X '' noetherianInfiniteDimensionBlock i :
            Set (MvPolynomial ℕ+ k)) := ⟨n, hn, rfl⟩
      have hpowmem : MvPolynomial.X n ^ (p.totalDegree + 1) ∈
          noetherianInfiniteDimensionBlockIdeal k i := by
        exact Ideal.pow_mem_of_mem _
          (Ideal.subset_span hxnmem) _ (by omega)
      simpa [noetherianInfiniteDimensionVariable] using
        Ideal.sub_mem _ hjmem hpowmem
    · exact hdisj j hji hx
  let R := NoetherianInfiniteDimensionPolynomialRing k
  let A := NoetherianInfiniteDimensionLocalization k
  let P : Ideal R := noetherianInfiniteDimensionBlockIdeal k i
  let M : Submonoid R := noetherianInfiniteDimensionMultiplicativeSet k
  let m : Ideal A := Ideal.map (algebraMap R A) P
  have hdisj' : Disjoint (M : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro x hxM hxP
    rw [noetherianInfiniteDimensionMultiplicativeSet_coe] at hxM
    exact (Set.mem_iInter.mp hxM i) hxP
  have hunder : m.under R = P := by
    exact IsLocalization.under_map_of_isPrime_disjoint M A
      (inferInstance : P.IsPrime) hdisj'
  have hm_ne_top : m ≠ ⊤ := by
    intro hm
    have hPtop : P = ⊤ := by
      rw [← hunder, hm]
      simp
    exact (inferInstance : P.IsPrime).ne_top hPtop
  change m.IsMaximal
  apply Ideal.isMaximal_iff.2
  constructor
  · intro hone
    apply hm_ne_top
    exact m.eq_top_iff_one.mpr hone
  · intro J x hmJ hxnot hxJ
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M x
    have hbJ : algebraMap R A b ∈ J := by
      rw [← IsLocalization.mk'_spec A b t]
      exact J.mul_mem_right _ hxJ
    have hbnot : b ∉ P := by
      intro hb
      apply hxnot
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      exact ⟨1, M.one_mem, by simpa using hb⟩
    let s := b + noetherianInfiniteDimensionVariable k n ^ (b.totalDegree + 1)
    have hs : s ∈ M := by
      simpa [s] using havoid b hbnot
    have hpowmem : MvPolynomial.X n ^ (b.totalDegree + 1) ∈ P := by
      have hxnmem : MvPolynomial.X n ∈
          (MvPolynomial.X '' noetherianInfiniteDimensionBlock i :
            Set (MvPolynomial ℕ+ k)) := ⟨n, hn, rfl⟩
      exact Ideal.pow_mem_of_mem _ (Ideal.subset_span hxnmem) _ (by omega)
    have hpowJ : algebraMap R A (MvPolynomial.X n ^ (b.totalDegree + 1)) ∈ J :=
      hmJ (Ideal.mem_map_of_mem _ hpowmem)
    have hsJ : algebraMap R A s ∈ J := by
      simpa [s, noetherianInfiniteDimensionVariable, map_add] using
        J.add_mem hbJ hpowJ
    have hsunit : IsUnit (algebraMap R A s) :=
      IsLocalization.map_units A ⟨s, hs⟩
    have htop : J = ⊤ := J.eq_top_of_isUnit_mem hsJ hsunit
    rw [htop]
    exact Submodule.mem_top

/-- The maximal ideals of `A` are exactly the ideals `𝔪ᵢ`. -/
theorem noetherianInfiniteDimension_isMaximal_iff
    (k : Type u) [Field k]
    (I : Ideal (NoetherianInfiniteDimensionLocalization k)) :
    I.IsMaximal ↔
      ∃ i : ℕ+, I = noetherianInfiniteDimensionLocalizedBlockIdeal k i := by
  classical
  let R := NoetherianInfiniteDimensionPolynomialRing k
  let A := NoetherianInfiniteDimensionLocalization k
  let M : Submonoid R := noetherianInfiniteDimensionMultiplicativeSet k
  let q : Ideal R := I.under R
  constructor
  · intro hI
    have hdisj : Disjoint (M : Set R) (q : Set R) := by
      rw [Set.disjoint_left]
      intro s hs hsq
      have hsI : algebraMap R A s ∈ I := by
        change algebraMap R A s ∈ I at hsq
        exact hsq
      have htop : I = ⊤ := I.eq_top_of_isUnit_mem hsI
        (IsLocalization.map_units A ⟨s, hs⟩)
      exact hI.ne_top htop
    have hqmem : ∀ p : R, p ∈ q → ∃ i : ℕ+,
        p ∈ noetherianInfiniteDimensionBlockIdeal k i := by
      intro p hp
      by_contra h
      push Not at h
      apply Set.disjoint_left.mp hdisj
      · rw [noetherianInfiniteDimensionMultiplicativeSet_coe]
        simp only [Set.mem_iInter, Set.mem_compl_iff]
        exact h
      · exact hp
    have hpowpred : ∀ n : ℕ, 0 < n → n ≤ 2 ^ (n - 1) := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
          cases n with
          | zero => simp
          | succ n =>
              intro hn
              have h := ih (by omega)
              rw [show Nat.succ (Nat.succ n) - 1 = n + 1 by omega, pow_succ]
              have hpowpos : 0 < 2 ^ n := by positivity
              have h' : n + 1 ≤ 2 ^ n := by simpa using h
              nlinarith
    let vars : R → Finset ℕ+ := fun p =>
      p.support.biUnion (fun m => m.support)
    let bound : R → ℕ+ := fun p =>
      ⟨1 + (vars p).sum (fun n => (n : ℕ)), by positivity⟩
    have hvar_bound : ∀ (p : R) (x : ℕ+), x ∈ vars p →
        (x : ℕ) ≤ bound p := by
      intro p x hx
      have hxsum : (x : ℕ) ≤ (vars p).sum (fun n => (n : ℕ)) := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
      change (x : ℕ) ≤ 1 + (vars p).sum (fun n => (n : ℕ))
      omega
    have hblock_bound : ∀ (p : R), p ≠ 0 → ∀ j : ℕ+,
        p ∈ noetherianInfiniteDimensionBlockIdeal k j → j ≤ bound p := by
      intro p hp0 j hpj
      obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp0
      change p ∈ Ideal.span (MvPolynomial.X ''
        noetherianInfiniteDimensionBlock j) at hpj
      rw [MvPolynomial.mem_ideal_span_X_image] at hpj
      obtain ⟨x, hx, hxm⟩ := hpj m hm
      have hxvars : x ∈ vars p := by
        exact Finset.mem_biUnion.mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hxm⟩
      have hxbound : (x : ℕ) ≤ bound p := hvar_bound p x hxvars
      change 2 ^ ((j : ℕ) - 1) ≤ (x : ℕ) ∧
        (x : ℕ) < 2 ^ (j : ℕ) at hx
      change (j : ℕ) ≤ (bound p : ℕ)
      exact (hpowpred (j : ℕ) j.2).trans (hx.1.trans hxbound)
    have hqle : ∃ i : ℕ+, q ≤ noetherianInfiniteDimensionBlockIdeal k i := by
      by_cases hqzero : q = ⊥
      · exact ⟨1, by simp [hqzero]⟩
      · have hqexist : ∃ f : R, f ∈ q ∧ f ≠ 0 := by
          by_contra h
          push Not at h
          apply hqzero
          apply le_antisymm
          · intro p hp
            simp [h p hp]
          · exact bot_le
        obtain ⟨f, hfq, hf0⟩ := hqexist
        let sf : Finset ℕ+ := (Finset.range (bound f : ℕ)).image
          (fun n : ℕ => ⟨n + 1, by omega⟩)
        have hsf : ∀ j : ℕ+, f ∈ noetherianInfiniteDimensionBlockIdeal k j →
            j ∈ sf := by
          intro j hj
          have hjle := hblock_bound f hf0 j hj
          have hjle' : (j : ℕ) ≤ (bound f : ℕ) := hjle
          have hbpos : 0 < (bound f : ℕ) := (bound f).2
          apply Finset.mem_image.mpr
          refine ⟨(j : ℕ) - 1, ?_, ?_⟩
          · apply Finset.mem_range.mpr
            omega
          · apply Subtype.ext
            exact Nat.sub_add_cancel j.2
        have hsf_le : ∀ j : ℕ+, j ∈ sf → j ≤ bound f := by
          intro j hj
          rcases Finset.mem_image.mp hj with ⟨a, ha, haj⟩
          have ha' := Finset.mem_range.mp ha
          have haj' : (j : ℕ) = a + 1 := by
            exact (congrArg Subtype.val haj).symm
          change (j : ℕ) ≤ (bound f : ℕ)
          omega
        have hblock_disjoint : ∀ (L : ℕ+) (n : ℕ+),
            n ∈ noetherianInfiniteDimensionBlock L → ∀ j : ℕ+,
              j ≠ L → n ∉ noetherianInfiniteDimensionBlock j := by
          intro L n hn j hji hj
          change 2 ^ ((L : ℕ) - 1) ≤ (n : ℕ) ∧
            (n : ℕ) < 2 ^ (L : ℕ) at hn
          rcases lt_or_gt_of_ne hji with hlt | hgt
          · have hpow' : 2 ^ (j : ℕ) ≤ 2 ^ ((L : ℕ) - 1) := by
              apply Nat.pow_le_pow_right (by omega)
              have hlt' : (j : ℕ) < (L : ℕ) := hlt
              omega
            change 2 ^ ((j : ℕ) - 1) ≤ (n : ℕ) ∧
              (n : ℕ) < 2 ^ (j : ℕ) at hj
            exact (not_lt_of_ge (hpow'.trans hn.1)) hj.2
          · have hpow' : 2 ^ (L : ℕ) ≤ 2 ^ ((j : ℕ) - 1) := by
              apply Nat.pow_le_pow_right (by omega)
              have hgt' : (L : ℕ) < (j : ℕ) := hgt
              omega
            change 2 ^ ((j : ℕ) - 1) ≤ (n : ℕ) ∧
              (n : ℕ) < 2 ^ (j : ℕ) at hj
            exact (not_le_of_gt hn.2) (hpow'.trans hj.1)
        have hcommon : ∀ g : R, g ∈ q → ∃ j ∈ sf,
            g ∈ noetherianInfiniteDimensionBlockIdeal k j := by
          intro g hgq
          by_contra hg
          push Not at hg
          let L : ℕ+ := bound f + bound g + 1
          let n : ℕ+ := ⟨2 ^ ((L : ℕ) - 1), by positivity⟩
          have hpowL : 2 ^ ((L : ℕ) - 1) < 2 ^ (L : ℕ) := by
            have hL : (L : ℕ) = ((L : ℕ) - 1) + 1 :=
              (Nat.sub_add_cancel L.2).symm
            have hpos : 0 < 2 ^ ((L : ℕ) - 1) := by positivity
            calc
              2 ^ ((L : ℕ) - 1) < 2 ^ ((L : ℕ) - 1) * 2 := by nlinarith
              _ = 2 ^ (((L : ℕ) - 1) + 1) :=
                (pow_succ 2 ((L : ℕ) - 1)).symm
              _ = 2 ^ (L : ℕ) := (congrArg (fun e : ℕ => 2 ^ e) hL).symm
          have hnblock : n ∈ noetherianInfiniteDimensionBlock L :=
            ⟨le_rfl, hpowL⟩
          have hLf : (bound f : ℕ) < (L : ℕ) := by
            dsimp [L]
            omega
          have hLg : (bound g : ℕ) < (L : ℕ) := by
            dsimp [L]
            omega
          have hnf : (bound f : ℕ) < (n : ℕ) := by
            change (bound f : ℕ) < 2 ^ ((L : ℕ) - 1)
            exact hLf.trans_le (hpowpred (L : ℕ) L.2)
          have hng : (bound g : ℕ) < (n : ℕ) := by
            change (bound g : ℕ) < 2 ^ ((L : ℕ) - 1)
            exact hLg.trans_le (hpowpred (L : ℕ) L.2)
          have hnfvars : n ∉ vars f := by
            intro hn
            exact (not_lt_of_ge (hvar_bound f n hn)) hnf
          have hngvars : n ∉ vars g := by
            intro hn
            exact (not_lt_of_ge (hvar_bound g n hn)) hng
          have hXnot : ∀ j : ℕ+, n ∉ noetherianInfiniteDimensionBlock j →
              noetherianInfiniteDimensionVariable k n ∉
                noetherianInfiniteDimensionBlockIdeal k j := by
            intro j hnj hX
            change MvPolynomial.X n ∈
              Ideal.span (MvPolynomial.X '' noetherianInfiniteDimensionBlock j) at hX
            rw [MvPolynomial.mem_ideal_span_X_image] at hX
            have hs : Finsupp.single n 1 ∈
                (MvPolynomial.X n : R).support := by simp
            obtain ⟨x, hx, hxs⟩ := hX _ hs
            have hxn : x = n := by
              by_contra hxn
              apply hxs
              simp [hxn]
            exact hnj (hxn ▸ hx)
          have hsum_mem : f + noetherianInfiniteDimensionVariable k n ^
              (f.totalDegree + 1) * g ∈ M := by
            change f + MvPolynomial.X n ^ (f.totalDegree + 1) * g ∈
              (M : Set R)
            rw [noetherianInfiniteDimensionMultiplicativeSet_coe]
            simp only [Set.mem_iInter, Set.mem_compl_iff]
            intro j
            change f + MvPolynomial.X n ^ (f.totalDegree + 1) * g ∉
              noetherianInfiniteDimensionBlockIdeal k j
            by_cases hfj : f ∈ noetherianInfiniteDimensionBlockIdeal k j
            · have hjsf : j ∈ sf := hsf j hfj
              have hgj : g ∉ noetherianInfiniteDimensionBlockIdeal k j := hg j hjsf
              have hjL : j ≠ L := by
                intro hjL
                subst j
                exact (not_lt_of_ge (hsf_le L hjsf)) hLf
              have hnj := hblock_disjoint L n hnblock j hjL
              have hXpow : MvPolynomial.X n ^ (f.totalDegree + 1) ∉
                  noetherianInfiniteDimensionBlockIdeal k j := by
                intro hpow
                exact (hXnot j hnj)
                  ((inferInstance :
                    (noetherianInfiniteDimensionBlockIdeal k j).IsPrime).mem_of_pow_mem _ hpow)
              have hprod : MvPolynomial.X n ^ (f.totalDegree + 1) * g ∉
                  noetherianInfiniteDimensionBlockIdeal k j :=
                (inferInstance :
                  (noetherianInfiniteDimensionBlockIdeal k j).IsPrime).mul_notMem hXpow hgj
              intro hsum
              apply hprod
              convert Ideal.sub_mem _ hsum hfj using 1; ring
            · have hfn : f ∉ noetherianInfiniteDimensionBlockIdeal k j := hfj
              change f ∉ Ideal.span (MvPolynomial.X '' noetherianInfiniteDimensionBlock j) at hfn
              rw [MvPolynomial.mem_ideal_span_X_image] at hfn
              push Not at hfn
              obtain ⟨m, hm, hmbad⟩ := hfn
              have hmprod : m ∉
                  (MvPolynomial.X n ^ (f.totalDegree + 1) * g).support := by
                intro hmprod
                have hmprod' := (MvPolynomial.support_mul _ _) hmprod
                obtain ⟨a, ha, b, hb, hab⟩ :
                    ∃ a ∈ (MvPolynomial.X n ^ (f.totalDegree + 1)).support,
                      ∃ b ∈ g.support, a + b = m := by
                  simpa [Finset.mem_add] using hmprod'
                have ha' : a = Finsupp.single n (f.totalDegree + 1) := by
                  rw [MvPolynomial.support_X_pow] at ha
                  exact Finset.mem_singleton.mp ha
                subst a
                have hdeg := MvPolynomial.le_totalDegree hm
                have hsum :
                    (Finsupp.single n (f.totalDegree + 1) + b).sum
                        (fun _ e => e) = f.totalDegree + 1 + b.sum (fun _ e => e) := by
                  rw [Finsupp.sum_add_index']
                  · rw [Finsupp.sum_single_index]
                    all_goals rfl
                  · intro _
                    rfl
                  · intro _ _ _
                    rfl
                rw [← hab, hsum] at hdeg
                omega
              have hm' : m ∈
                  MvPolynomial.support (f + MvPolynomial.X n ^ (f.totalDegree + 1) * g) := by
                apply Finsupp.mem_support_iff.mpr
                change MvPolynomial.coeff m
                  (f + MvPolynomial.X n ^ (f.totalDegree + 1) * g) ≠ 0
                rw [MvPolynomial.coeff_add, MvPolynomial.notMem_support_iff.mp hmprod]
                simpa only [add_zero] using MvPolynomial.mem_support_iff.mp hm
              intro hsum
              change f + MvPolynomial.X n ^ (f.totalDegree + 1) * g ∈ Ideal.span
                (MvPolynomial.X '' noetherianInfiniteDimensionBlock j) at hsum
              rw [MvPolynomial.mem_ideal_span_X_image] at hsum
              obtain ⟨x, hx, hxm⟩ := hsum m hm'
              exact hxm (hmbad x hx)
          have hsum_q : f + MvPolynomial.X n ^ (f.totalDegree + 1) * g ∈ q := by
            exact q.add_mem hfq (q.mul_mem_left _ hgq)
          exact (Set.disjoint_left.mp hdisj) hsum_mem hsum_q
        have hqsub : (q : Set R) ⊆ ⋃ j ∈ (sf : Set ℕ+),
            (noetherianInfiniteDimensionBlockIdeal k j : Set R) := by
          intro g hgq
          obtain ⟨j, hjsf, hgj⟩ := hcommon g hgq
          exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hjsf, hgj⟩⟩
        obtain ⟨i, hi, hqi⟩ :=
          (Ideal.subset_union_prime_finite (Finset.finite_toSet sf) 1 1
            (fun j _ _ _ => inferInstance)).mp hqsub
        exact ⟨i, hqi⟩
    obtain ⟨i, hqi⟩ := hqle
    have hPdisj : Disjoint (M : Set R)
        (noetherianInfiniteDimensionBlockIdeal k i : Set R) := by
      rw [Set.disjoint_left]
      intro s hs hsP
      rw [noetherianInfiniteDimensionMultiplicativeSet_coe] at hs
      exact (Set.mem_iInter.mp hs i) hsP
    have hPunder :
        (noetherianInfiniteDimensionLocalizedBlockIdeal k i).under R =
          noetherianInfiniteDimensionBlockIdeal k i := by
      exact IsLocalization.under_map_of_isPrime_disjoint M A
        (inferInstance :
          (noetherianInfiniteDimensionBlockIdeal k i).IsPrime) hPdisj
    have hIle : I ≤ noetherianInfiniteDimensionLocalizedBlockIdeal k i := by
      apply (IsLocalization.under_le_under_iff M A).mp
      change q ≤ _
      rw [hPunder]
      exact hqi
    have hm_ne_top : noetherianInfiniteDimensionLocalizedBlockIdeal k i ≠ ⊤ := by
      intro hm_top
      have hPtop : noetherianInfiniteDimensionBlockIdeal k i = ⊤ := by
        rw [← hPunder, hm_top]
        simp
      exact (inferInstance :
        (noetherianInfiniteDimensionBlockIdeal k i).IsPrime).ne_top hPtop
    exact ⟨i, hI.eq_of_le hm_ne_top hIle⟩
  · rintro ⟨i, rfl⟩
    infer_instance

/-- The localizations `A_{𝔪ᵢ}` and `R_{𝔭ᵢ}` are canonically isomorphic as
algebras over `R`. -/
theorem noetherianInfiniteDimension_localization_at_maximal_equiv
    (k : Type u) [Field k] (i : ℕ+) :
    Nonempty
      (Localization.AtPrime
          (noetherianInfiniteDimensionLocalizedBlockIdeal k i) ≃ₐ[
            NoetherianInfiniteDimensionPolynomialRing k]
        Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i)) := by
  classical
  let R := NoetherianInfiniteDimensionPolynomialRing k
  let A := NoetherianInfiniteDimensionLocalization k
  let P : Ideal R := noetherianInfiniteDimensionBlockIdeal k i
  let M : Submonoid R := noetherianInfiniteDimensionMultiplicativeSet k
  let Q : Ideal A := noetherianInfiniteDimensionLocalizedBlockIdeal k i
  have hdisj : Disjoint (M : Set R) (P : Set R) := by
    rw [Set.disjoint_left]
    intro x hxM hxP
    rw [noetherianInfiniteDimensionMultiplicativeSet_coe] at hxM
    exact (Set.mem_iInter.mp hxM i) hxP
  have hunder : Q.under R = P := by
    exact IsLocalization.under_map_of_isPrime_disjoint M A
      (inferInstance : P.IsPrime) hdisj
  have hcomap : Q.comap (algebraMap R A) = P := by
    simpa only [Ideal.under_def] using hunder
  have hcomap' : Q.comap (algebraMap R (Localization M)) = P := by
    simpa [A] using hcomap
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M Q
  let F : {p : Ideal R // p.IsPrime} → Type u := fun p =>
    Localization (@Ideal.primeCompl R _ p.1 p.2)
  let pP : {p : Ideal R // p.IsPrime} := ⟨P, inferInstance⟩
  let pC : {p : Ideal R // p.IsPrime} :=
    ⟨Q.comap (algebraMap R (Localization M)), inferInstance⟩
  have hp : pP = pC := by
    apply Subtype.ext
    exact hcomap'.symm
  let c : F pP ≃ₐ[R] F pC := AlgEquiv.cast hp
  have he : Localization.AtPrime P ≃ₐ[R] Localization.AtPrime Q := by
    change F pP ≃ₐ[R] Localization.AtPrime Q
    exact c.trans e
  exact ⟨he.symm⟩

/-- The ring `R_{𝔭ᵢ}` is Noetherian, local, and has the dimension of its
finite block of variables.  The source writes this dimension as `2^i`, but
the displayed block has `2^(i - 1)` variables, so the statement below uses
the mathematically correct value. -/
theorem noetherianInfiniteDimension_block_localization_properties
    (k : Type u) [Field k] (i : ℕ+) :
    IsNoetherianRing
        (Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i)) ∧
      IsLocalRing
        (Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i)) ∧
      ringKrullDim
          (Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i)) =
        (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞) := by
  classical
  let s : Set ℕ+ := noetherianInfiniteDimensionBlock i
  let e0 : MvPolynomial ℕ+ k ≃ₐ[k]
      MvPolynomial s (MvPolynomial {n : ℕ+ // n ∉ s} k) :=
    (MvPolynomial.renameEquiv k (Equiv.Set.sumCompl s).symm).trans
      (MvPolynomial.sumAlgEquiv k s {n : ℕ+ // n ∉ s})
  have hPmap :
      Ideal.map e0.toRingEquiv (noetherianInfiniteDimensionBlockIdeal k i) =
        MvPolynomial.idealOfVars s (MvPolynomial {n : ℕ+ // n ∉ s} k) := by
    rw [noetherianInfiniteDimensionBlockIdeal, MvPolynomial.idealOfVars,
      Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨n, hn, rfl⟩, rfl⟩
      have hn' : n ∈ s := hn
      refine ⟨⟨n, hn'⟩, ?_⟩
      simp [e0, noetherianInfiniteDimensionVariable,
        Equiv.Set.sumCompl_symm_apply_of_mem hn', MvPolynomial.sumAlgEquiv_X_inl]
    · rintro ⟨a, rfl⟩
      refine ⟨MvPolynomial.X (Equiv.Set.sumCompl s (Sum.inl a)), ?_, ?_⟩
      · exact ⟨Equiv.Set.sumCompl s (Sum.inl a), by
          exact a.property, rfl⟩
      · simp [e0, MvPolynomial.sumAlgEquiv_X_inl]
  let B := MvPolynomial {n : ℕ+ // n ∉ s} k
  let K := FractionRing B
  let R' := MvPolynomial s B
  let S' := MvPolynomial s K
  let qB := MvPolynomial.idealOfVars s B
  let qK := MvPolynomial.idealOfVars s K
  let N := (nonZeroDivisors B).map (MvPolynomial.C : B →+* R')
  letI : Algebra R' S' := MvPolynomial.algebraMvPolynomial
  haveI : qB.IsPrime := mvPolynomial_idealOfVars_isPrime B s
  haveI : qK.IsPrime := mvPolynomial_idealOfVars_isPrime K s
  have hqmap :
      Ideal.map (algebraMap R' S') qB = qK := by
    change Ideal.map (algebraMap (MvPolynomial s B) (MvPolynomial s K))
        (MvPolynomial.idealOfVars s B) = MvPolynomial.idealOfVars s K
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, by simp⟩
    · rintro ⟨a, rfl⟩
      exact ⟨MvPolynomial.X a, ⟨a, rfl⟩, by simp⟩
  have hdisj : Disjoint (N : Set R') (qB : Set R') := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmq
    change MvPolynomial.C m ∈ MvPolynomial.idealOfVars s B at hmq
    have hmq' : MvPolynomial.C m ∈ Ideal.span
        (MvPolynomial.X '' (Set.univ : Set s)) := by
      simpa only [MvPolynomial.idealOfVars, Set.image_univ] using hmq
    rw [MvPolynomial.mem_ideal_span_X_image] at hmq'
    have hm0 : m ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hm
    have hzero : (0 : s →₀ ℕ) ∈ (MvPolynomial.C m : MvPolynomial s B).support := by
      rw [MvPolynomial.mem_support_iff]
      simp [hm0]
    obtain ⟨a, ha, hna⟩ := hmq' 0 hzero
    simpa using hna
  have hunder :
      (Ideal.map (algebraMap R' S') qB).under R' = qB :=
    IsLocalization.under_map_of_isPrime_disjoint N S' inferInstance hdisj
  have hqcomap : qK.comap (algebraMap R' S') = qB := by
    change qK.under R' = qB
    rw [← hqmap]
    exact hunder
  let eS : S' ≃ₐ[R'] Localization N :=
    IsLocalization.algEquiv N S' (Localization N)
  let qL : Ideal (Localization N) := Ideal.map eS.toRingEquiv qK
  haveI : qL.IsPrime := by
    dsimp [qL]
    infer_instance
  have hqmapL :
      Ideal.map (algebraMap R' (Localization N)) qB = qL := by
    calc
      Ideal.map (algebraMap R' (Localization N)) qB =
          Ideal.map eS.toRingEquiv (Ideal.map (algebraMap R' S') qB) := by
        change Ideal.map (algebraMap R' (Localization N)) qB =
          Ideal.map eS.toRingEquiv.toRingHom
            (Ideal.map (algebraMap R' S') qB)
        rw [Ideal.map_map]
        have hcomp : eS.toRingEquiv.toRingHom.comp (algebraMap R' S') =
            algebraMap R' (Localization N) := by
          apply RingHom.ext
          intro x
          exact eS.commutes x
        rw [hcomp]
      _ = qL := by rw [hqmap]
  have hqcomapL : qL.comap (algebraMap R' (Localization N)) = qB := by
    change qL.under R' = qB
    rw [← hqmapL]
    exact IsLocalization.under_map_of_isPrime_disjoint N (Localization N)
      inferInstance hdisj
  have hsfin : s.Finite := by
    dsimp [s, noetherianInfiniteDimensionBlock]
    exact Set.finite_Ico _ _
  haveI := hsfin.fintype
  have hfinite := finiteMvPolynomial_idealOfVars_localization_properties_finite K s
  have hqmapKL : Ideal.map eS.toRingEquiv qK = qL := rfl
  have hM : qK.primeCompl.map eS.toRingEquiv = qL.primeCompl := by
    ext x
    constructor
    · intro hx
      rcases (Submonoid.mem_map.mp hx) with ⟨y, hy, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hy ⊢
      intro hey
      apply hy
      have hy' : y ∈ qL.comap eS.toRingEquiv := hey
      have hcomapKL : qL.comap eS.toRingEquiv = qK := by
        ext z
        rw [Ideal.mem_comap, ← hqmapKL, Ideal.apply_mem_of_equiv_iff]
      rw [hcomapKL] at hy'
      exact hy'
    · intro hx
      obtain ⟨y, rfl⟩ := eS.toRingEquiv.surjective x
      apply Submonoid.mem_map.mpr
      refine ⟨y, ?_, rfl⟩
      rw [Ideal.mem_primeCompl_iff] at hx ⊢
      intro hy
      apply hx
      have hy' : eS y ∈ Ideal.map eS.toRingEquiv qK :=
        Ideal.mem_map_of_mem eS.toRingEquiv hy
      rw [hqmapKL] at hy'
      exact hy'
  let eKtoL : Localization.AtPrime qK ≃+* Localization.AtPrime qL :=
    IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime qK) (Localization.AtPrime qL) eS.toRingEquiv hM
  let eBloc : Localization.AtPrime qB ≃ₐ[R'] Localization.AtPrime qL :=
    localization_atPrime_algEquiv_of_comap_eq
      (R := R') N qL (P := qB) hqcomapL
  have hPmap' : Ideal.map e0.toRingEquiv (noetherianInfiniteDimensionBlockIdeal k i) = qB := by
    simpa [qB, B] using hPmap
  let eP :
      Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i) ≃+*
        Localization.AtPrime qB :=
    localization_atPrime_ringEquiv_of_map_eq
      (R := MvPolynomial ℕ+ k) (S := R')
      (P := noetherianInfiniteDimensionBlockIdeal k i) (Q := qB)
      e0.toRingEquiv hPmap'
  let eAll :
      Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i) ≃+*
        Localization.AtPrime qK :=
    eP.trans (eBloc.toRingEquiv.trans eKtoL.symm)
  have hcard : Nat.card s = 2 ^ ((i : ℕ) - 1) := by
    let a : ℕ+ := ⟨2 ^ ((i : ℕ) - 1), by positivity⟩
    let b : ℕ+ := ⟨2 ^ (i : ℕ), by positivity⟩
    have hs_eq : s = Set.Ico a b := by
      rfl
    rw [hs_eq, Nat.card_eq_fintype_card, PNat.card_fintype_Ico]
    norm_num [a, b]
  haveI := hfinite.1
  haveI := hfinite.2.1
  refine ⟨isNoetherianRing_of_ringEquiv _ eAll.symm, ?_, ?_⟩
  · exact eAll.symm.isLocalRing
  · rw [ringKrullDim_eq_of_ringEquiv eAll]
    change ringKrullDim (Localization.AtPrime
        (MvPolynomial.idealOfVars s K)) =
      (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞)
    calc
      _ = (↑(Nat.card s) : WithBot ℕ∞) := hfinite.2.2
      _ = _ := by rw [hcard]

/-- The Nagata localization `A` is Noetherian. -/
private theorem finite_noetherianInfiniteDimensionBlockIdeal_mem
    {k : Type u} [Field k] (p : NoetherianInfiniteDimensionPolynomialRing k)
    (hp : p ≠ 0) :
    {i : ℕ+ | p ∈ noetherianInfiniteDimensionBlockIdeal k i}.Finite := by
  let vars : Finset ℕ+ := p.support.biUnion (fun m => m.support)
  let bound : ℕ+ := ⟨1 + (vars.sum (fun n => (n : ℕ))), by positivity⟩
  have hpowpred : ∀ n : ℕ, 0 < n → n ≤ 2 ^ (n - 1) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        cases n with
        | zero => simp
        | succ n =>
            intro hn
            have h := ih (by omega)
            rw [show Nat.succ (Nat.succ n) - 1 = n + 1 by omega, pow_succ]
            have hpowpos : 0 < 2 ^ n := by positivity
            have h' : n + 1 ≤ 2 ^ n := by simpa using h
            nlinarith
  have hvar_bound : ∀ (x : ℕ+), x ∈ vars → (x : ℕ) ≤ bound := by
    intro x hx
    have hxsum : (x : ℕ) ≤ vars.sum (fun n => (n : ℕ)) := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx
    change (x : ℕ) ≤ 1 + vars.sum (fun n => (n : ℕ))
    omega
  apply (Set.finite_Iic bound).subset
  intro j hj
  change j ≤ bound
  have hblock : p ∈ Ideal.span (MvPolynomial.X ''
      noetherianInfiniteDimensionBlock j) := by
    change p ∈ Ideal.span (MvPolynomial.X '' noetherianInfiniteDimensionBlock j) at hj
    exact hj
  rw [MvPolynomial.mem_ideal_span_X_image] at hblock
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hp
  obtain ⟨x, hx, hxm⟩ := hblock m hm
  have hxvars : x ∈ vars := by
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hxm⟩
  have hxbound : (x : ℕ) ≤ bound := hvar_bound x hxvars
  change 2 ^ ((j : ℕ) - 1) ≤ (x : ℕ) ∧
    (x : ℕ) < 2 ^ (j : ℕ) at hx
  exact (hpowpred (j : ℕ) j.2).trans (hx.1.trans hxbound)

private theorem localized_ideal_fg_generators
    {A : Type*} [CommRing A] (I : Ideal A) (P : Ideal A) [P.IsMaximal]
    (hI : (I.map (algebraMap A (Localization.AtPrime P))).FG) :
    ∃ T : Set A, T.Finite ∧ T ⊆ I ∧
      I.map (algebraMap A (Localization.AtPrime P)) =
        (Ideal.span T).map (algebraMap A (Localization.AtPrime P)) := by
  classical
  let S := Localization.AtPrime P
  let f := algebraMap A S
  rcases Submodule.fg_def.mp hI with ⟨G, hGfin, hGspan⟩
  haveI := hGfin.fintype
  have hmem : ∀ z : G, z.1 ∈ I.map f := by
    intro z
    rw [← hGspan]
    exact Submodule.subset_span z.2
  have hz : ∀ z : G, ∃ xt : I × P.primeCompl,
      z.1 * f xt.2 = f xt.1 := by
    intro z
    exact (IsLocalization.mem_map_algebraMap_iff P.primeCompl S).mp (hmem z)
  choose xt hxt using hz
  let x : ∀ z : G, I := fun z => (xt z).1
  let t : ∀ z : G, P.primeCompl := fun z => (xt z).2
  let T : Set A := (fun z : G => (x z : A)) '' Set.univ
  have hTfin : T.Finite := by
    dsimp [T]
    exact (Set.toFinite (Set.univ : Set G)).image _
  have hTsub : T ⊆ I := by
    rintro y ⟨z, -, rfl⟩
    exact (x z).2
  refine ⟨T, hTfin, hTsub, ?_⟩
  apply le_antisymm
  · rw [← hGspan]
    apply Ideal.span_le.2
    intro z hzG
    apply (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S (t ⟨z, hzG⟩))).mp
    have hxin : (x ⟨z, hzG⟩ : A) ∈ T := by
      exact ⟨⟨z, hzG⟩, Set.mem_univ _, rfl⟩
    have heq : (algebraMap A S) (t ⟨z, hzG⟩ : A) * z =
        f (x ⟨z, hzG⟩) := by
      rw [mul_comm]
      exact hxt ⟨z, hzG⟩
    rw [heq]
    exact Ideal.mem_map_of_mem f (Ideal.subset_span hxin)
  · apply Ideal.map_mono
    exact Ideal.span_le.2 hTsub

private theorem finite_noetherianInfiniteDimension_maximals_containing
    {k : Type u} [Field k]
    (f : NoetherianInfiniteDimensionLocalization k) (hf : f ≠ 0) :
    {Q : Ideal (NoetherianInfiniteDimensionLocalization k) |
      Q.IsMaximal ∧ f ∈ Q}.Finite := by
  let R := NoetherianInfiniteDimensionPolynomialRing k
  let A := NoetherianInfiniteDimensionLocalization k
  let M : Submonoid R := noetherianInfiniteDimensionMultiplicativeSet k
  obtain ⟨p, m, hpm⟩ := IsLocalization.exists_mk'_eq M f
  have hp : p ≠ 0 := by
    intro hp
    apply hf
    simpa [hp] using hpm.symm
  have hblocks : {i : ℕ+ | p ∈ noetherianInfiniteDimensionBlockIdeal k i}.Finite :=
    finite_noetherianInfiniteDimensionBlockIdeal_mem p hp
  have hsub :
      {Q : Ideal A | Q.IsMaximal ∧ f ∈ Q} ⊆
        (fun i : ℕ+ => noetherianInfiniteDimensionLocalizedBlockIdeal k i) ''
          {i : ℕ+ | p ∈ noetherianInfiniteDimensionBlockIdeal k i} := by
    intro Q hQ
    obtain ⟨i, hi⟩ := (noetherianInfiniteDimension_isMaximal_iff k Q).mp hQ.1
    refine ⟨i, ?_, hi.symm⟩
    have hfi : f ∈ noetherianInfiniteDimensionLocalizedBlockIdeal k i := by
      simpa [hi] using hQ.2
    have hpi : algebraMap R A p ∈
        noetherianInfiniteDimensionLocalizedBlockIdeal k i := by
      apply (IsLocalization.mk'_mem_iff (M := M) (S := A)).mp
      rw [hpm]
      exact hfi
    have hunder :
        (noetherianInfiniteDimensionLocalizedBlockIdeal k i).under R =
          noetherianInfiniteDimensionBlockIdeal k i := by
      apply IsLocalization.under_map_of_isPrime_disjoint M A
        (inferInstance :
          (noetherianInfiniteDimensionBlockIdeal k i).IsPrime)
      rw [Set.disjoint_left]
      intro s hs hsP
      rw [noetherianInfiniteDimensionMultiplicativeSet_coe] at hs
      exact (Set.mem_iInter.mp hs i) hsP
    change p ∈ (noetherianInfiniteDimensionLocalizedBlockIdeal k i).under R at hpi
    rw [hunder] at hpi
    exact hpi
  exact (hblocks.image (fun i : ℕ+ =>
    noetherianInfiniteDimensionLocalizedBlockIdeal k i)).subset hsub

instance noetherianInfiniteDimensionLocalization_isNoetherian
    (k : Type u) [Field k] :
    IsNoetherianRing (NoetherianInfiniteDimensionLocalization k) := by
  classical
  let R := NoetherianInfiniteDimensionPolynomialRing k
  let A := NoetherianInfiniteDimensionLocalization k
  let M : Submonoid R := noetherianInfiniteDimensionMultiplicativeSet k
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases hI : I = ⊥
  · rw [hI]
    exact Submodule.fg_bot
  obtain ⟨f, hfI, hf0⟩ : ∃ f : A, f ∈ I ∧ f ≠ 0 := by
    by_contra h
    push Not at h
    apply hI
    apply le_antisymm
    · intro x hx
      by_contra hx0
      exact hx0 (h x hx)
    · exact bot_le
  let maxs : Set (Ideal A) := {Q | Q.IsMaximal ∧ f ∈ Q}
  have hmaxs : maxs.Finite := by
    exact finite_noetherianInfiniteDimension_maximals_containing f hf0
  have hlocalNoeth : ∀ (P : Ideal A) (_ : P.IsMaximal),
      IsNoetherianRing (Localization.AtPrime P) := by
    intro P hP
    obtain ⟨i, hi⟩ := (noetherianInfiniteDimension_isMaximal_iff k P).mp hP
    subst P
    haveI : IsNoetherianRing
        (Localization.AtPrime (noetherianInfiniteDimensionBlockIdeal k i)) :=
      (noetherianInfiniteDimension_block_localization_properties k i).1
    rcases noetherianInfiniteDimension_localization_at_maximal_equiv k i with ⟨e⟩
    exact isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv
  haveI : ∀ Q : maxs, Q.1.IsMaximal := fun Q => Q.2.1
  haveI : ∀ Q : maxs, Q.1.IsPrime := fun Q => Q.2.1.isPrime'
  have hlocalfg : ∀ Q : maxs,
      (I.map (algebraMap A (Localization.AtPrime Q.1))).FG := by
    intro Q
    haveI : IsNoetherianRing (Localization.AtPrime Q.1) :=
      hlocalNoeth Q.1 Q.2.1
    exact IsNoetherian.noetherian _
  have hgen : ∀ Q : maxs, ∃ T : Set A, T.Finite ∧ T ⊆ I ∧
      I.map (algebraMap A (Localization.AtPrime Q.1)) =
        (Ideal.span T).map (algebraMap A (Localization.AtPrime Q.1)) := by
    intro Q
    exact localized_ideal_fg_generators I Q.1 (hlocalfg Q)
  choose T hTfin hTsub hTmap using hgen
  haveI := hmaxs.fintype
  let U : Set A := {f} ∪ ⋃ Q : maxs, T Q
  have hUfin : U.Finite := by
    dsimp [U]
    exact (Set.finite_singleton f).union (Set.finite_iUnion fun Q => hTfin Q)
  have hUsub : U ⊆ I := by
    intro x hx
    simp only [U, Set.mem_union, Set.mem_singleton_iff, Set.mem_iUnion] at hx
    rcases hx with rfl | ⟨Q, hQ⟩
    · exact hfI
    · exact hTsub Q hQ
  let J : Ideal A := Ideal.span U
  have hJfg : J.FG := by
    exact Submodule.fg_def.mpr ⟨U, hUfin, rfl⟩
  have hlocal_eq : ∀ (P : Ideal A) (_ : P.IsMaximal),
      I.map (algebraMap A (Localization.AtPrime P)) =
        J.map (algebraMap A (Localization.AtPrime P)) := by
    intro P hP
    by_cases hfp : f ∈ P
    · let Q : maxs := ⟨P, hP, hfp⟩
      have hTQU : T Q ⊆ U := by
        intro x hx
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨Q, hx⟩)
      have hleft : I.map (algebraMap A (Localization.AtPrime P)) ≤
          J.map (algebraMap A (Localization.AtPrime P)) := by
        rw [hTmap Q]
        apply Ideal.map_mono
        exact Ideal.span_mono hTQU
      have hright : J.map (algebraMap A (Localization.AtPrime P)) ≤
          I.map (algebraMap A (Localization.AtPrime P)) := by
        apply Ideal.map_mono
        dsimp [J]
        exact Ideal.span_le.2 hUsub
      exact le_antisymm hleft hright
    · have hunit : IsUnit
          (algebraMap A (Localization.AtPrime P) f) :=
        IsLocalization.map_units (Localization.AtPrime P)
          (⟨f, hfp⟩ : P.primeCompl)
      have htopI : I.map (algebraMap A (Localization.AtPrime P)) = ⊤ :=
        (I.map (algebraMap A (Localization.AtPrime P))).eq_top_of_isUnit_mem
          (Ideal.mem_map_of_mem _ hfI) hunit
      have hfU : f ∈ U := Set.mem_union_left _ (Set.mem_singleton f)
      have htopJ : J.map (algebraMap A (Localization.AtPrime P)) = ⊤ :=
        (J.map (algebraMap A (Localization.AtPrime P))).eq_top_of_isUnit_mem
          (Ideal.mem_map_of_mem _ (Ideal.subset_span hfU)) hunit
      rw [htopI, htopJ]
  rw [Ideal.eq_of_localization_maximal hlocal_eq]
  exact hJfg

/-- The Nagata localization has infinite Krull dimension. -/
theorem noetherianInfiniteDimensionLocalization_has_infinite_dimension
    (k : Type u) [Field k] :
    ringKrullDim (NoetherianInfiniteDimensionLocalization k) = ⊤ := by
  classical
  let A := NoetherianInfiniteDimensionLocalization k
  rw [ENat.WithBot.eq_top_iff_forall_ge]
  intro n
  have hpow : n ≤ 2 ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hpowpos : 0 < 2 ^ n := by positivity
        nlinarith
  let i : ℕ+ := ⟨n + 1, by omega⟩
  let Q : Ideal A := noetherianInfiniteDimensionLocalizedBlockIdeal k i
  haveI : Q.IsMaximal := by
    dsimp [Q]
    infer_instance
  haveI : Q.IsPrime := inferInstance
  have hlocaldim : ringKrullDim (Localization.AtPrime Q) =
      (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞) := by
    rcases noetherianInfiniteDimension_localization_at_maximal_equiv k i with ⟨e⟩
    rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    exact (noetherianInfiniteDimension_block_localization_properties k i).2.2
  have hheight : Q.height =
      (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞) := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height Q
      (Localization.AtPrime Q)]
    exact hlocaldim
  have hglobal :
      (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by
    rw [← hheight]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  apply (show (n : WithBot ℕ∞) ≤
      (↑(2 ^ ((i : ℕ) - 1) : ℕ) : WithBot ℕ∞) from ?_).trans hglobal
  change (n : WithBot ℕ∞) ≤ (↑(2 ^ n : ℕ) : WithBot ℕ∞)
  exact_mod_cast hpow

/-- The construction is a Noetherian ring of infinite dimension. -/
theorem noetherianInfiniteDimension_example
    (k : Type u) [Field k] :
    IsNoetherianRing (NoetherianInfiniteDimensionLocalization k) ∧
      ringKrullDim (NoetherianInfiniteDimensionLocalization k) = ⊤ :=
  ⟨inferInstance, noetherianInfiniteDimensionLocalization_has_infinite_dimension k⟩

end Formalization.Books.Examples.Unit16
