import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 6: Explicit polynomial spectra

The polynomial rings, the map used in the two-variable hint, and the
localizing submonoid are defined explicitly.  Prime classification and
topological descriptions are recorded as theorem interfaces; their proofs
belong to the later prove stage.
-/

noncomputable section

universe u

open Set Topology

namespace Formalization.Books.Exercises.Unit06

/-! ## `Spec(k[x])` -/

/-- The one-variable polynomial ring in the notation of the source. -/
abbrev oneVariablePolynomialRing (k : Type u) [Field k] := Polynomial k

/-- The generic point of `Spec(k[x])`. -/
def polynomialGenericPoint (k : Type u) [Field k] :
    PrimeSpectrum (oneVariablePolynomialRing k) :=
  ⟨⊥, by infer_instance⟩

/-- Over an arbitrary field, the nonzero prime ideals of `k[x]` are generated
by irreducible polynomials. -/
theorem polynomial_spectrum_prime_ideals (k : Type u) [Field k] :
    ∀ p : PrimeSpectrum (oneVariablePolynomialRing k),
      p.asIdeal = ⊥ ∨
        ∃ f : Polynomial k, f ≠ 0 ∧ Irreducible f ∧
          p.asIdeal = Ideal.span {f} := by
  intro p
  rcases (Ideal.isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors).mp p.2 with
    hbot | ⟨f, hf, h⟩
  · exact Or.inl hbot
  · exact Or.inr ⟨f, hf.ne_zero, hf.irreducible, h⟩

/-- Over an algebraically closed field, the nonzero primes are the maximal
ideals `(x - a)`. -/
theorem polynomial_spectrum_prime_ideals_alg_closed
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∀ p : PrimeSpectrum (oneVariablePolynomialRing k),
      p.asIdeal = ⊥ ∨
        ∃ a : k,
          p.asIdeal =
            Ideal.span {Polynomial.X - Polynomial.C a} := by
  intro p
  rcases polynomial_spectrum_prime_ideals k p with hbot | ⟨f, hf0, hf, hp⟩
  · exact Or.inl hbot
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_root f (Polynomial.degree_pos_of_irreducible hf).ne'
    refine Or.inr ⟨a, ?_⟩
    rw [hp, Ideal.span_singleton_eq_span_singleton]
    exact ((Polynomial.irreducible_X_sub_C a).associated_of_dvd hf
      (Polynomial.dvd_iff_isRoot.mpr ha)).symm

/-- The closed sets of `Spec(k[x])` are the whole space and finite sets of
closed points. -/
theorem polynomial_spectrum_closed_sets (k : Type u) [Field k]
    (Z : Set (PrimeSpectrum (oneVariablePolynomialRing k))) :
    IsClosed Z ↔
      Z = Set.univ ∨ (Z.Finite ∧ polynomialGenericPoint k ∉ Z) := by
  classical
  constructor
  · intro hZ
    by_cases hg : polynomialGenericPoint k ∈ Z
    · left
      apply Set.eq_univ_of_forall
      intro p
      have hcl : closure ({polynomialGenericPoint k} : Set (PrimeSpectrum (oneVariablePolynomialRing k))) ⊆ Z :=
        hZ.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hg)
      apply hcl
      rw [PrimeSpectrum.closure_singleton]
      exact (PrimeSpectrum.mem_zeroLocus p (polynomialGenericPoint k).asIdeal).2 (by
        change (⊥ : Ideal (oneVariablePolynomialRing k)) ≤ p.asIdeal
        exact bot_le)
    · right
      rcases (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ with ⟨S, hSZ⟩
      have hSf : ∃ f ∈ S, f ≠ 0 := by
        by_contra h
        apply hg
        rw [hSZ]
        apply (PrimeSpectrum.mem_zeroLocus (polynomialGenericPoint k) S).2
        intro f hf
        by_contra hf0
        exact h ⟨f, hf, hf0⟩
      obtain ⟨f, hfS, hf0⟩ := hSf
      let hpoint : Polynomial k → PrimeSpectrum (oneVariablePolynomialRing k) := fun g =>
        if hg : g ∈ UniqueFactorizationMonoid.factors f then
          ⟨Ideal.span {g},
            Ideal.isPrime_span_singleton_of_prime
              (UniqueFactorizationMonoid.irreducible_of_factor g hg).prime⟩
        else polynomialGenericPoint k
      refine ⟨(UniqueFactorizationMonoid.factors f).toFinset.finite_toSet.image hpoint |>.subset ?_, hg⟩
      intro p hpZ
      have hpbot : p.asIdeal ≠ (⊥ : Ideal (oneVariablePolynomialRing k)) := by
        intro hp
        apply hg
        have heq : p = polynomialGenericPoint k := by
          apply PrimeSpectrum.ext
          change p.asIdeal = (⊥ : Ideal (oneVariablePolynomialRing k))
          exact hp
        exact heq ▸ hpZ
      rcases polynomial_spectrum_prime_ideals k p with hzero | ⟨g, hg0, hgi, hpg⟩
      · exact (hpbot hzero).elim
      · have hmem : f ∈ p.asIdeal :=
          (PrimeSpectrum.mem_zeroLocus p S).1 (hSZ ▸ hpZ) hfS
        have hga : g ∣ f := by
          rw [hpg] at hmem
          exact Ideal.mem_span_singleton.mp hmem
        obtain ⟨q, hq, hgq⟩ :=
          UniqueFactorizationMonoid.exists_mem_factors_of_dvd hf0 hgi hga
        have hpq : p = hpoint q := by
          apply PrimeSpectrum.ext
          simp only [hpoint, dif_pos hq]
          exact hpg.trans (Ideal.span_singleton_eq_span_singleton.mpr hgq)
        refine ⟨q, ?_, hpq.symm⟩
        simpa using hq
  · rintro (rfl | ⟨hfin, hg⟩)
    · exact isClosed_univ
    · rw [← Set.biUnion_of_singleton Z]
      exact hfin.isClosed_biUnion (fun p hp => by
        apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).2
        have hpbot : p.asIdeal ≠ (⊥ : Ideal (oneVariablePolynomialRing k)) := by
          intro hpzero
          have heq : p = polynomialGenericPoint k := by
            apply PrimeSpectrum.ext
            change p.asIdeal = (⊥ : Ideal (oneVariablePolynomialRing k))
            exact hpzero
          exact hg (heq ▸ hp)
        rcases polynomial_spectrum_prime_ideals k p with hzero | ⟨f, hf0, hf, hpf⟩
        · exact (hpbot hzero).elim
        · rw [hpf]
          exact PrincipalIdealRing.isMaximal_of_irreducible hf)

/-- The standard opens give the topology on `Spec(k[x])`. -/
theorem polynomial_spectrum_standard_open_basis (k : Type u) [Field k] :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : Polynomial k =>
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (oneVariablePolynomialRing k)))) := by
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

/-- Specialization in `Spec(k[x])` is inclusion of prime ideals. -/
theorem polynomial_spectrum_specialization_iff (k : Type u) [Field k]
    (p q : PrimeSpectrum (oneVariablePolynomialRing k)) :
    p ⤳ q ↔ p.asIdeal ≤ q.asIdeal := by
  exact (PrimeSpectrum.le_iff_specializes p q).symm

/-- The generic point specializes to every point of `Spec(k[x])`. -/
theorem polynomial_generic_point_specializes_every_point (k : Type u) [Field k]
    (p : PrimeSpectrum (oneVariablePolynomialRing k)) :
    polynomialGenericPoint k ⤳ p := by
  simpa only [polynomial_spectrum_specialization_iff, polynomialGenericPoint] using
    (bot_le : (⊥ : Ideal (oneVariablePolynomialRing k)) ≤ p.asIdeal)

/-! ## `Spec(k[x,y])` and its map to `Spec(k[x])` -/

/-- The two-variable polynomial ring used for affine 2-space. -/
abbrev twoVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k

/-- The inclusion of the `x`-axis coefficient polynomial ring into the
two-variable polynomial ring. -/
def polynomialXInclusion (k : Type u) [Field k] :
    Polynomial k →+* twoVariablePolynomialRing k :=
  Polynomial.eval₂RingHom
    (MvPolynomial.C : k →+* twoVariablePolynomialRing k)
    (MvPolynomial.X (0 : Fin 2))

/-- The morphism `Spec(k[x,y]) → Spec(k[x])` from the source hint. -/
def polynomialSpectrumMap (k : Type u) [Field k] :
    PrimeSpectrum (twoVariablePolynomialRing k) →
      PrimeSpectrum (oneVariablePolynomialRing k) :=
  PrimeSpectrum.comap (polynomialXInclusion k)

/-- The multiplicative subset of nonzero one-variable polynomials used in
the generic-fibre localization hint. -/
def nonzeroPolynomialSubmonoid (k : Type u) [Field k] : Submonoid (Polynomial k) where
  carrier := {f | f ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := by
    intro f g hf hg
    exact mul_ne_zero hf hg

/-- The localization of `k[x]` at all nonzero polynomials. -/
abbrev nonzeroPolynomialLocalization (k : Type u) [Field k] :=
  Localization (nonzeroPolynomialSubmonoid k)

/-- The multiplicative subset of `k[x,y]` obtained by mapping the nonzero
one-variable polynomials along the displayed inclusion. -/
def nonzeroPolynomialImageSubmonoid (k : Type u) [Field k] :
    Submonoid (twoVariablePolynomialRing k) :=
  (nonzeroPolynomialSubmonoid k).map (polynomialXInclusion k)

/-- The localization of `k[x,y]` used by the generic-fibre hint. -/
abbrev nonzeroPolynomialFiberLocalization (k : Type u) [Field k] :=
  Localization (nonzeroPolynomialImageSubmonoid k)

/-- Prime ideals of the generic-fibre localization correspond to prime ideals
of `k[x,y]` disjoint from the image of the nonzero polynomials in `k[x]`. -/
noncomputable def polynomial_spectrum_generic_fiber_localization_order_iso
    (k : Type u) [Field k] :
    PrimeSpectrum (nonzeroPolynomialFiberLocalization k) ≃o
      {p : PrimeSpectrum (twoVariablePolynomialRing k) //
        Disjoint (nonzeroPolynomialImageSubmonoid k :
          Set (twoVariablePolynomialRing k)) p.asIdeal} := by
  exact IsLocalization.primeSpectrumOrderIso
    (nonzeroPolynomialImageSubmonoid k) (nonzeroPolynomialFiberLocalization k)

/-- The generic fibre of the displayed map is the locus where the induced
prime of `k[x]` is zero. -/
theorem polynomial_spectrum_generic_fiber_preimage (k : Type u) [Field k] :
    polynomialSpectrumMap k ⁻¹'
      ({polynomialGenericPoint k} : Set (PrimeSpectrum (oneVariablePolynomialRing k))) =
      {p : PrimeSpectrum (twoVariablePolynomialRing k) |
        Ideal.comap (polynomialXInclusion k) p.asIdeal = ⊥} := by
  apply Set.ext
  intro p
  change polynomialSpectrumMap k p = polynomialGenericPoint k ↔
    Ideal.comap (polynomialXInclusion k) p.asIdeal = ⊥
  exact ⟨
    (fun h => by
      simpa [polynomialSpectrumMap, polynomialGenericPoint] using
        congrArg PrimeSpectrum.asIdeal h),
    (fun h => by
      apply PrimeSpectrum.ext
      simpa [polynomialSpectrumMap, polynomialGenericPoint] using h)
    ⟩

/-- Disjointness from the image of the nonzero `k[x]` polynomials is the
generic-fibre condition for the displayed spectrum map. -/
theorem polynomial_spectrum_generic_fiber_disjoint_iff
    (k : Type u) [Field k] (p : PrimeSpectrum (twoVariablePolynomialRing k)) :
    Disjoint (nonzeroPolynomialImageSubmonoid k : Set (twoVariablePolynomialRing k))
        p.asIdeal ↔
      Ideal.comap (polynomialXInclusion k) p.asIdeal = ⊥ := by
  exact ⟨
    (fun h => by
      apply le_antisymm ?_ bot_le
      intro f hf
      by_contra hf0
      exact (Set.disjoint_left.1 h)
        (show polynomialXInclusion k f ∈
            (nonzeroPolynomialImageSubmonoid k : Set (twoVariablePolynomialRing k)) from
          ⟨f, hf0, rfl⟩) hf),
    (fun h => by
      apply Set.disjoint_left.2
      intro x hxS hxI
      rcases hxS with ⟨f, hf, rfl⟩
      apply hf
      have hfI : f ∈ Ideal.comap (polynomialXInclusion k) p.asIdeal := hxI
      rw [h] at hfI
      exact hfI)
    ⟩

/-- Over an algebraically closed field, the primes of `k[x,y]` are zero, a
principal prime generated by an irreducible polynomial, or a maximal ideal
of a point `(a,b)`. -/
theorem two_variable_spectrum_prime_ideals_alg_closed
    (k : Type u) [Field k] [IsAlgClosed k] :
    ∀ p : PrimeSpectrum (twoVariablePolynomialRing k),
      p.asIdeal = ⊥ ∨
        (∃ f : twoVariablePolynomialRing k,
          Irreducible f ∧ p.asIdeal = Ideal.span {f}) ∨
        (∃ a b : k,
          p.asIdeal =
            Ideal.span
              ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a,
                MvPolynomial.X (1 : Fin 2) - MvPolynomial.C b} :
              Set (twoVariablePolynomialRing k))) := by
  intro p
  let _ : p.asIdeal.IsPrime := p.2
  by_cases hpbot : p.asIdeal = (⊥ : Ideal (twoVariablePolynomialRing k))
  · exact Or.inl hpbot
  right
  by_cases hpmax : p.asIdeal.IsMaximal
  · obtain ⟨x, hx⟩ :=
      MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal k hpmax
    let a : k := x (0 : Fin 2)
    let b : k := x (1 : Fin 2)
    have hxvec : x = ![a, b] := by
      funext i
      fin_cases i <;> rfl
    refine Or.inr ⟨a, b, ?_⟩
    let e := Polynomial.Bivariate.equivMvPolynomial k
    let I : Ideal (Polynomial (Polynomial k)) :=
      Ideal.span
        ({(Polynomial.C ((Polynomial.X : Polynomial k) - Polynomial.C a) :
              Polynomial (Polynomial k)),
          (Polynomial.X : Polynomial (Polynomial k)) -
              Polynomial.C (Polynomial.C b)} :
          Set (Polynomial (Polynomial k)))
    have hmap : Ideal.map (e : Polynomial (Polynomial k) →+* twoVariablePolynomialRing k) I =
        Ideal.span
          ({MvPolynomial.X (0 : Fin 2) - MvPolynomial.C a,
            MvPolynomial.X (1 : Fin 2) - MvPolynomial.C b} :
          Set (twoVariablePolynomialRing k)) := by
      rw [Ideal.map_span]
      congr 1
      ext q
      constructor
      · rintro ⟨q, hq, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl <;> simp [e]
      · intro hq
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
        rcases hq with rfl | rfl
        · exact ⟨Polynomial.C Polynomial.X - Polynomial.C (Polynomial.C a),
            by simp, by simp [e]⟩
        · exact ⟨(Polynomial.X : Polynomial (Polynomial k)) -
              Polynomial.C (Polynomial.C b), by simp, by simp [e]⟩
    have heval (q : twoVariablePolynomialRing k) :
        ((e.symm q).eval (Polynomial.C b)).eval a =
          MvPolynomial.aeval ![a, b] q := by
      let F : twoVariablePolynomialRing k →+* k :=
        (Polynomial.evalRingHom a).comp
          ((Polynomial.evalRingHom (Polynomial.C b)).comp
            (e.symm : twoVariablePolynomialRing k →+* Polynomial (Polynomial k)))
      have hF : F = (MvPolynomial.aeval (R := k) ![a, b]).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [F, e]
        · intro i
          fin_cases i <;> simp [F, e]
      simpa [F] using congrArg (fun f => f q) hF
    rw [hx]
    apply le_antisymm
    · intro q hq
      have hq0 : MvPolynomial.aeval (R := k) x q = 0 :=
        (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).mp hq
      rw [hxvec] at hq0
      have hr : e.symm q ∈ I := by
        change e.symm q ∈ Ideal.span
          ({(Polynomial.C ((Polynomial.X : Polynomial k) - Polynomial.C a) :
                Polynomial (Polynomial k)),
            (Polynomial.X : Polynomial (Polynomial k)) -
                Polynomial.C (Polynomial.C b)} :
            Set (Polynomial (Polynomial k)))
        rw [Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero]
        calc
          ((e.symm q).eval (Polynomial.C b)).eval a =
              MvPolynomial.aeval (R := k) ![a, b] q := heval q
          _ = 0 := hq0
      rw [← hmap]
      exact (Ideal.mem_map_iff_of_surjective e e.surjective).mpr
        ⟨e.symm q, hr, e.apply_symm_apply q⟩
    · intro q hq
      apply (MvPolynomial.mem_vanishingIdeal_singleton_iff x q).2
      rw [hxvec]
      have hqmap : q ∈ Ideal.map (e : Polynomial (Polynomial k) →+* twoVariablePolynomialRing k) I := by
        rw [hmap]
        exact hq
      obtain ⟨r, hr, hreq⟩ :=
        (Ideal.mem_map_iff_of_surjective e e.surjective).mp hqmap
      change r ∈ Ideal.span
        ({(Polynomial.C ((Polynomial.X : Polynomial k) - Polynomial.C a) :
              Polynomial (Polynomial k)),
          (Polynomial.X : Polynomial (Polynomial k)) -
              Polynomial.C (Polynomial.C b)} :
          Set (Polynomial (Polynomial k))) at hr
      rw [Polynomial.mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero] at hr
      calc
        MvPolynomial.aeval (R := k) ![a, b] q =
            ((e.symm q).eval (Polynomial.C b)).eval a := (heval q).symm
        _ = ((e.symm (e r)).eval (Polynomial.C b)).eval a := by
          congr 2
          exact congrArg e.symm hreq.symm
        _ = ((r.eval (Polynomial.C b)).eval a) := by rw [e.symm_apply_apply]
        _ = 0 := hr
  · have hdim : ringKrullDim (twoVariablePolynomialRing k) = (2 : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
      simp [ringKrullDim_eq_zero_of_field]
    let _ : FiniteRingKrullDim (twoVariablePolynomialRing k) :=
      finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨by
        rw [hdim]
        exact WithBot.coe_ne_bot, by
        rw [hdim]
        change ((2 : ℕ∞) : WithBot ℕ∞) ≠ ⊤
        intro h
        exact (ENat.natCast_ne_top 2) (WithBot.coe_eq_top.mp h)⟩
    have hle' : (p.asIdeal.height : WithBot ℕ∞) ≤ ringKrullDim (twoVariablePolynomialRing k) :=
      Ideal.height_le_ringKrullDim_of_ne_top (I := p.asIdeal) Ideal.IsPrime.ne_top'
    rw [hdim] at hle'
    have hle : p.asIdeal.height ≤ 2 := WithBot.coe_le_coe.mp hle'
    have hzero : p.asIdeal.height ≠ 0 := by
      intro hh
      exact hpbot (Ideal.height_eq_zero_iff_eq_bot.mp hh)
    have hne : p.asIdeal.height ≠ 2 := by
      intro hh
      apply hpmax
      apply Ideal.isMaximal_of_height_eq_ringKrullDim
      exact (congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hh).trans hdim.symm
    have hone : p.asIdeal.height = 1 := by
      apply (Order.le_one_iff.mp (ENat.lt_two_iff.mp (lt_of_le_of_ne hle hne))).resolve_left
      exact hzero
    obtain ⟨f, hf⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hone
    have hf0 : f ≠ 0 := by
      intro hfzero
      apply hpbot
      rw [hf, hfzero]
      simp
    have hprime : (Ideal.span {f}).IsPrime := by
      rw [show Ideal.span {f} = p.asIdeal by simpa using hf.symm]
      exact inferInstance
    exact Or.inl ⟨f,
      ((Ideal.span_singleton_prime hf0).mp hprime).irreducible,
      hf⟩

/-- Closed subsets of affine 2-space are exactly the Zariski zero loci. -/
theorem two_variable_spectrum_closed_sets (k : Type u) [Field k]
    (Z : Set (PrimeSpectrum (twoVariablePolynomialRing k))) :
    IsClosed Z ↔
      ∃ S : Set (twoVariablePolynomialRing k),
        Z = PrimeSpectrum.zeroLocus S := by
  exact PrimeSpectrum.isClosed_iff_zeroLocus Z

/-! ## `Spec(ℤ[y])` -/

/-- The polynomial ring in the final exercise. -/
abbrev integerPolynomialRing : Type := Polynomial ℤ

/-- The coefficient inclusion `ℤ → ℤ[y]`. -/
def integerPolynomialBaseMap : ℤ →+* integerPolynomialRing :=
  Polynomial.C

/-- The spectrum map used in the localization hint for `Spec(ℤ[y])`. -/
def integerPolynomialSpectrumMap :
    PrimeSpectrum integerPolynomialRing → PrimeSpectrum ℤ :=
  PrimeSpectrum.comap integerPolynomialBaseMap

/-- The nonzero integers used in the generic-fibre localization for
`Spec(ℤ[y])`. -/
def nonzeroIntegerSubmonoid : Submonoid ℤ where
  carrier := {n | n ≠ 0}
  one_mem' := one_ne_zero
  mul_mem' := by
    intro m n hm hn
    exact mul_ne_zero hm hn

/-- The image in `ℤ[y]` of the nonzero integers. -/
def nonzeroIntegerImageSubmonoid : Submonoid integerPolynomialRing :=
  (nonzeroIntegerSubmonoid.map integerPolynomialBaseMap)

/-- The localization of `ℤ[y]` used by the final exercise's generic-fibre
hint. -/
abbrev nonzeroIntegerPolynomialFiberLocalization : Type :=
  Localization nonzeroIntegerImageSubmonoid

/-- Prime ideals of the generic-fibre localization of `ℤ[y]` correspond to
prime ideals of `ℤ[y]` disjoint from the nonzero integers. -/
noncomputable def integer_polynomial_generic_fiber_localization_order_iso :
    PrimeSpectrum nonzeroIntegerPolynomialFiberLocalization ≃o
      {P : PrimeSpectrum integerPolynomialRing //
        Disjoint (nonzeroIntegerImageSubmonoid : Set integerPolynomialRing) P.asIdeal} := by
  exact IsLocalization.primeSpectrumOrderIso
    nonzeroIntegerImageSubmonoid nonzeroIntegerPolynomialFiberLocalization

/-- The zero-prime fibre of `Spec(ℤ[y]) → Spec(ℤ)` is characterized by
disjointness from the image of the nonzero integers. -/
theorem integer_polynomial_generic_fiber_preimage :
    integerPolynomialSpectrumMap ⁻¹'
      ({⟨⊥, by infer_instance⟩} : Set (PrimeSpectrum ℤ)) =
      {P : PrimeSpectrum integerPolynomialRing |
        Ideal.comap integerPolynomialBaseMap P.asIdeal = ⊥} := by
  ext P
  change integerPolynomialSpectrumMap P = (⟨⊥, by infer_instance⟩ : PrimeSpectrum ℤ) ↔
    Ideal.comap integerPolynomialBaseMap P.asIdeal = ⊥
  constructor
  · intro h
    simpa [integerPolynomialSpectrumMap] using
      congrArg PrimeSpectrum.asIdeal h
  · intro h
    apply PrimeSpectrum.ext
    simpa [integerPolynomialSpectrumMap] using h

theorem integer_polynomial_generic_fiber_disjoint_iff
    (P : PrimeSpectrum integerPolynomialRing) :
    Disjoint (nonzeroIntegerImageSubmonoid : Set integerPolynomialRing) P.asIdeal ↔
      Ideal.comap integerPolynomialBaseMap P.asIdeal = ⊥ := by
  exact ⟨
    (fun h => by
      apply le_antisymm ?_ bot_le
      intro n hn
      by_contra hn0
      exact (Set.disjoint_left.1 h)
        (show integerPolynomialBaseMap n ∈
            (nonzeroIntegerImageSubmonoid : Set integerPolynomialRing) from
          ⟨n, hn0, rfl⟩) hn),
    (fun h => by
      apply Set.disjoint_left.2
      intro x hxS hxI
      rcases hxS with ⟨n, hn, rfl⟩
      apply hn
      have hnI : n ∈ Ideal.comap integerPolynomialBaseMap P.asIdeal := hxI
      rw [h] at hnI
      exact hnI)
    ⟩

/-- The maximal ideals of `ℤ[y]` are the inverse images of irreducible
polynomial ideals over residue fields `𝔽_p`. -/
def integerPolynomialMaximalIdeal (p : ℕ) (g : Polynomial (ZMod p)) :
    Ideal integerPolynomialRing :=
  Ideal.comap (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
    (Ideal.span {g})

/-- Every maximal ideal of `ℤ[y]` has the displayed residue-field form. -/
theorem integer_polynomial_maximal_ideal_classification
    (I : Ideal integerPolynomialRing) :
    I.IsMaximal ↔
      ∃ p : ℕ, ∃ hp : Nat.Prime p, ∃ g : Polynomial (ZMod p),
        Irreducible g ∧ I = integerPolynomialMaximalIdeal p g := by
  sorry

/-- The primes of `ℤ[y]` are zero, principal primes generated by irreducible
polynomials, or maximal ideals. -/
theorem integer_polynomial_spectrum_prime_ideals :
    ∀ P : PrimeSpectrum integerPolynomialRing,
      P.asIdeal = ⊥ ∨
        (∃ f : integerPolynomialRing,
          Irreducible f ∧ P.asIdeal = Ideal.span {f}) ∨
        P.asIdeal.IsMaximal := by
  sorry

/-- The topology of `Spec(ℤ[y])` is the Zariski topology described by zero
loci, with standard opens as its basis. -/
theorem integer_polynomial_spectrum_closed_sets
    (Z : Set (PrimeSpectrum integerPolynomialRing)) :
    IsClosed Z ↔
      ∃ S : Set integerPolynomialRing,
        Z = PrimeSpectrum.zeroLocus S := by
  exact PrimeSpectrum.isClosed_iff_zeroLocus Z

theorem integer_polynomial_spectrum_standard_open_basis :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : integerPolynomialRing =>
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum integerPolynomialRing))) := by
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

end Formalization.Books.Exercises.Unit06
