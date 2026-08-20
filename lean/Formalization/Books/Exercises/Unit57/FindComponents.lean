import Formalization.Books.Exercises.Unit57.Definitions

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 57: components of a coordinate hypersurface

The four-variable polynomial ring is represented by `MvPolynomial (Fin 4) k`,
with indices `0, 1, 2, 3` corresponding to `x, y, z, w`.  Components of the
zero locus are written as subsets of the zero-locus subtype, matching
Mathlib's `irreducibleComponents` interface for a closed subspace.
-/

namespace Formalization.Books.Exercises.Unit57

open Set

universe u

noncomputable section

private theorem ker_span_variables2
    {R : Type u} [CommRing R] {σ : Type*} (s : Finset σ) :
    RingHom.ker
        ((MvPolynomial.killCompl
          (Subtype.val_injective : Function.Injective
            (fun i : {i : σ // i ∉ s} => i.1))).toRingHom) =
      (Ideal.span (MvPolynomial.X '' (s : Set σ)) :
        Ideal (MvPolynomial σ R)) := by
  classical
  let f : MvPolynomial σ R →+* MvPolynomial {i : σ // i ∉ s} R :=
    (MvPolynomial.killCompl
      (Subtype.val_injective : Function.Injective
        (fun i : {i : σ // i ∉ s} => i.1))).toRingHom
  have hker : RingHom.ker f = Ideal.span (MvPolynomial.X '' (s : Set σ)) := by
    apply le_antisymm
    · intro p hp
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      by_contra hno
      have hsub : (m.support : Set σ) ⊆
          Set.range (fun i : {i : σ // i ∉ s} => i.1) := by
        intro i hi
        by_cases his : i ∈ s
        · exact False.elim (hno ⟨i, his, Finsupp.mem_support_iff.mp hi⟩)
        · exact ⟨⟨i, his⟩, rfl⟩
      let n : {i : σ // i ∉ s} →₀ ℕ :=
        Finsupp.comapDomain (fun i : {i : σ // i ∉ s} => i.1) m
          (Subtype.val_injective.injOn)
      have hmap : Finsupp.mapDomain
            (fun i : {i : σ // i ∉ s} => i.1) n = m := by
        exact Finsupp.mapDomain_comapDomain _ Subtype.val_injective m hsub
      have hp' : (f p).coeff n = 0 := by
        rw [hp]
        simp
      have hcoeff : p.coeff m = 0 := by
        simpa [f, n, MvPolynomial.coeff_killCompl, hmap] using hp'
      exact (Finsupp.mem_support_iff.mp hm) hcoeff
    · rw [Ideal.span_le]
      rintro _ ⟨i, his, rfl⟩
      have hirange : i ∉ Set.range
          (fun j : {j : σ // j ∉ s} => j.1) := by
        rintro ⟨j, hj⟩
        exact j.2 (by simpa [hj] using his)
      change f (MvPolynomial.X i) = 0
      change (MvPolynomial.killCompl
        (Subtype.val_injective : Function.Injective
          (fun j : {j : σ // j ∉ s} => j.1))) (MvPolynomial.X i) = 0
      rw [MvPolynomial.killCompl, MvPolynomial.aeval_X]
      exact dif_neg hirange
  exact hker

private theorem span_X_of_finset_isPrime
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type*} (s : Finset σ) :
    (Ideal.span (MvPolynomial.X '' (s : Set σ)) : Ideal (MvPolynomial σ R)).IsPrime := by
  rw [← ker_span_variables2 s]
  exact RingHom.ker_isPrime _

private def quotient_span_X_finset_ringEquiv
    {R : Type u} [CommRing R] {σ : Type*} (s : Finset σ) :
    (MvPolynomial σ R ⧸ (Ideal.span (MvPolynomial.X '' (s : Set σ)) :
      Ideal (MvPolynomial σ R))) ≃+*
      MvPolynomial {i : σ // i ∉ s} R := by
  classical
  let κ : MvPolynomial σ R →+* MvPolynomial {i : σ // i ∉ s} R :=
    (MvPolynomial.killCompl
      (Subtype.val_injective : Function.Injective
        (fun i : {i : σ // i ∉ s} => i.1))).toRingHom
  have hsurj : Function.Surjective κ := by
    intro q
    refine ⟨MvPolynomial.rename (fun i : {i : σ // i ∉ s} => i.1) q, ?_⟩
    simp [κ]
  let e :
      (MvPolynomial σ R ⧸ RingHom.ker κ) ≃+*
        MvPolynomial {i : σ // i ∉ s} R :=
    RingHom.quotientKerEquivOfSurjective (f := κ) hsurj
  rw [ker_span_variables2 s] at e
  exact e

/-! ## The polynomial ring, ideal, and its two candidate components -/

abbrev fourVariablePolynomialRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 4) k

def coordinateXIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 4)} : Set (fourVariablePolynomialRing k))

def coordinateYZWIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (3 : Fin 4)} : Set (fourVariablePolynomialRing k))

def coordinateVarietyIdeal (k : Type u) [Field k] :
    Ideal (fourVariablePolynomialRing k) :=
  Ideal.span
    ({MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4),
      MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4),
      MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (3 : Fin 4)} :
      Set (fourVariablePolynomialRing k))

def coordinateVariety (k : Type u) [Field k] :
    Set (PrimeSpectrum (fourVariablePolynomialRing k)) :=
  PrimeSpectrum.zeroLocus (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k))

def coordinateXComponent (k : Type u) [Field k] :
    Set (coordinateVariety k) :=
  {p | (p : PrimeSpectrum (fourVariablePolynomialRing k)) ∈
    PrimeSpectrum.zeroLocus (coordinateXIdeal k : Set (fourVariablePolynomialRing k))}

def coordinateYZWComponent (k : Type u) [Field k] :
    Set (coordinateVariety k) :=
  {p | (p : PrimeSpectrum (fourVariablePolynomialRing k)) ∈
    PrimeSpectrum.zeroLocus (coordinateYZWIdeal k : Set (fourVariablePolynomialRing k))}

/-! ## Exercise `find-components` -/

/-- The two irreducible components of `V(xy, xz, xw)` are `V(x)` and
`V(y,z,w)`, of dimensions three and one respectively. -/
theorem irreducible_components_of_coordinate_variety
    (k : Type u) [Field k] :
    (coordinateVarietyIdeal k).minimalPrimes =
        {coordinateXIdeal k, coordinateYZWIdeal k} ∧
      irreducibleComponents (coordinateVariety k) =
        {coordinateXComponent k, coordinateYZWComponent k} ∧
      ringKrullDim
          (fourVariablePolynomialRing k ⧸ coordinateXIdeal k) =
        (3 : WithBot ℕ∞) ∧
      ringKrullDim
          (fourVariablePolynomialRing k ⧸ coordinateYZWIdeal k) =
        (1 : WithBot ℕ∞) := by
  classical
  have hXprime : (coordinateXIdeal k).IsPrime := by
    have h := span_X_of_finset_isPrime (R := k) ({0} : Finset (Fin 4))
    simpa [coordinateXIdeal] using h
  have hYprime : (coordinateYZWIdeal k).IsPrime := by
    have h := span_X_of_finset_isPrime (R := k) ({1, 2, 3} : Finset (Fin 4))
    have hset : MvPolynomial.X '' (({1, 2, 3} : Finset (Fin 4)) : Set (Fin 4)) =
        ({MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
          MvPolynomial.X (3 : Fin 4)} : Set (fourVariablePolynomialRing k)) := by
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        simp at hi ⊢
        rcases hi with rfl | rfl | rfl <;> simp
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨1, by simp, rfl⟩
        · exact ⟨2, by simp, rfl⟩
        · exact ⟨3, by simp, rfl⟩
    have h' : (Ideal.span
        ({MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
          MvPolynomial.X (3 : Fin 4)} : Set (fourVariablePolynomialRing k))).IsPrime := by
      rw [hset] at h
      exact h
    simpa [coordinateYZWIdeal] using h'
  have hXleI : coordinateVarietyIdeal k ≤ coordinateXIdeal k := by
    rw [coordinateVarietyIdeal]
    refine Ideal.span_le.mpr ?_
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl <;>
      exact (coordinateXIdeal k).mul_mem_right _
        (Ideal.subset_span (by simp))
  have hYleI : coordinateVarietyIdeal k ≤ coordinateYZWIdeal k := by
    rw [coordinateVarietyIdeal]
    refine Ideal.span_le.mpr ?_
    · intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with (rfl | rfl | rfl)
      · exact (coordinateYZWIdeal k).mul_mem_left _
          (Ideal.subset_span (by simp))
      · exact (coordinateYZWIdeal k).mul_mem_left _
          (Ideal.subset_span (by simp))
      · exact (coordinateYZWIdeal k).mul_mem_left _
          (Ideal.subset_span (by simp))
  have hX1notX : MvPolynomial.X (1 : Fin 4) ∉ coordinateXIdeal k := by
    rw [coordinateXIdeal]
    have heq : ({MvPolynomial.X (0 : Fin 4)} : Set (fourVariablePolynomialRing k)) =
        MvPolynomial.X '' ({0} : Set (Fin 4)) := by
      ext z
      simp
    rw [heq, MvPolynomial.mem_ideal_span_X_image]
    intro h
    obtain ⟨i, hi, hmi⟩ := h (Finsupp.single (1 : Fin 4) 1) (by simp)
    simp at hi
    subst i
    simp at hmi
  have hX0notY : MvPolynomial.X (0 : Fin 4) ∉ coordinateYZWIdeal k := by
    rw [coordinateYZWIdeal]
    have heq : ({MvPolynomial.X (1 : Fin 4), MvPolynomial.X (2 : Fin 4),
        MvPolynomial.X (3 : Fin 4)} : Set (fourVariablePolynomialRing k)) =
        MvPolynomial.X '' ({1, 2, 3} : Set (Fin 4)) := by
      ext z
      constructor
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨1, by simp, rfl⟩
        · exact ⟨2, by simp, rfl⟩
        · exact ⟨3, by simp, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        simp at hi ⊢
        rcases hi with rfl | rfl | rfl <;> simp
    rw [heq, MvPolynomial.mem_ideal_span_X_image]
    intro h
    obtain ⟨i, hi, hmi⟩ := h (Finsupp.single (0 : Fin 4) 1) (by simp)
    rcases (by simpa using hi) with rfl | rfl | rfl <;> simp at hmi
  have hXmin : coordinateXIdeal k ∈
      (coordinateVarietyIdeal k).minimalPrimes := by
    refine ⟨⟨hXprime, hXleI⟩, ?_⟩
    intro q hq hqle
    have hprod : MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4) ∈ q :=
      hq.2 (Ideal.subset_span (by simp))
    rcases hq.1.mem_or_mem hprod with hx | hy
    · exact Ideal.span_le.mpr (by
        intro z hz
        rcases hz with rfl
        exact hx)
    · exact False.elim (hX1notX (hqle (by simpa [coordinateXIdeal] using hy)))
  have hYmin : coordinateYZWIdeal k ∈
      (coordinateVarietyIdeal k).minimalPrimes := by
    refine ⟨⟨hYprime, hYleI⟩, ?_⟩
    intro q hq hqle
    have hmem (i : Fin 4) (hi : i = 1 ∨ i = 2 ∨ i = 3) :
        MvPolynomial.X i ∈ q := by
      have hprod : MvPolynomial.X (0 : Fin 4) * MvPolynomial.X i ∈ q := by
        rcases hi with rfl | rfl | rfl <;>
          exact hq.2 (Ideal.subset_span (by simp))
      rcases hq.1.mem_or_mem hprod with hx | hy
      · exact False.elim (hX0notY (hqle (by simpa [coordinateYZWIdeal] using hx)))
      · exact hy
    refine Ideal.span_le.mpr ?_
    rintro z (rfl | rfl | rfl) <;>
      exact hmem _ (by simp)
  have hmin : (coordinateVarietyIdeal k).minimalPrimes =
      {coordinateXIdeal k, coordinateYZWIdeal k} := by
    ext p
    constructor
    · intro hp
      by_cases hx : MvPolynomial.X (0 : Fin 4) ∈ p
      · have hle : coordinateXIdeal k ≤ p := by
          rw [coordinateXIdeal]
          exact Ideal.span_le.mpr (by
            intro z hz
            rcases hz with rfl
            exact hx)
        have hple : p ≤ coordinateXIdeal k := hp.2
          ⟨hXprime, hXleI⟩ hle
        exact Set.mem_insert_iff.mpr (Or.inl (le_antisymm hple hle))
      · have hle : coordinateYZWIdeal k ≤ p := by
          rw [coordinateYZWIdeal]
          refine Ideal.span_le.mpr ?_
          rintro z (rfl | rfl | rfl)
          · have hprod : MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (1 : Fin 4) ∈ p :=
              hp.1.2 (Ideal.subset_span (by simp))
            rcases hp.1.1.mem_or_mem hprod with hx' | hy
            · exact False.elim (hx hx')
            · exact hy
          · have hprod : MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (2 : Fin 4) ∈ p :=
              hp.1.2 (Ideal.subset_span (by simp))
            rcases hp.1.1.mem_or_mem hprod with hx' | hy
            · exact False.elim (hx hx')
            · exact hy
          · have hprod : MvPolynomial.X (0 : Fin 4) * MvPolynomial.X (3 : Fin 4) ∈ p :=
              hp.1.2 (Ideal.subset_span (by simp))
            rcases hp.1.1.mem_or_mem hprod with hx' | hy
            · exact False.elim (hx hx')
            · exact hy
        have hple : p ≤ coordinateYZWIdeal k := hp.2
          ⟨hYprime, hYleI⟩ hle
        exact Set.mem_insert_iff.mpr (Or.inr (le_antisymm hple hle))
    · intro hp
      rcases hp with rfl | rfl
      · exact hXmin
      · exact hYmin
  constructor
  · exact hmin
  constructor
  · rw [irreducibleComponents_eq_maximals_closed]
    let e : {p : Ideal (fourVariablePolynomialRing k) |
        p.IsPrime ∧ coordinateVarietyIdeal k ≤ p} ≃o coordinateVariety k :=
      ⟨⟨fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
        fun x => ⟨x.1.1, x.1.2, x.2⟩, fun _ => rfl, fun _ => rfl⟩, .rfl⟩
    let g := e.trans ((PrimeSpectrum.zeroLocusEquivIrreducibleCloseds
        (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k))).trans
      (TopologicalSpace.IrreducibleCloseds.orderIsoSubtype'
        (coordinateVariety k)).dual)
    have g_apply (p : {p : Ideal (fourVariablePolynomialRing k) |
        p.IsPrime ∧ coordinateVarietyIdeal k ≤ p}) :
        (g p).1 = {q : coordinateVariety k |
          p.1 ≤ (q : PrimeSpectrum (fourVariablePolynomialRing k)).asIdeal} := by
      simp [g, e, PrimeSpectrum.zeroLocusEquivIrreducibleCloseds,
        TopologicalSpace.IrreducibleCloseds.orderIsoSubtype',
        TopologicalSpace.IrreducibleCloseds.equivSubtype',
        irreducibleSetEquivPoints]
      ext q
      change q ∈ closure ({(⟨⟨p.1, p.2.1⟩, p.2.2⟩ :
        PrimeSpectrum.zeroLocus
          (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k))) } :
        Set (PrimeSpectrum.zeroLocus
          (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k)))) ↔ _
      constructor
      · intro hq
        exact (PrimeSpectrum.le_iff_specializes _ _).mpr
          ((subtype_specializes_iff _ _).mp ((specializes_iff_mem_closure).mpr hq))
      · intro hq
        have hs : (⟨⟨p.1, p.2.1⟩, p.2.2⟩ :
            PrimeSpectrum.zeroLocus
              (coordinateVarietyIdeal k : Set (fourVariablePolynomialRing k))) ⤳ q :=
          (subtype_specializes_iff _ _).mpr
            ((PrimeSpectrum.le_iff_specializes _ _).mp hq)
        exact (specializes_iff_mem_closure).mp hs
    let hcomp := OrderIso.setOfPredMinimalIsoSetOfPredMaximal g
    have hcomp_apply (p : (coordinateVarietyIdeal k).minimalPrimes) :
        (OrderDual.ofDual (hcomp p).1 : Set (coordinateVariety k)) =
          {q : coordinateVariety k |
            p.1 ≤ (q : PrimeSpectrum (fourVariablePolynomialRing k)).asIdeal} := by
      change (OrderDual.ofDual (g (⟨p.1, p.2.1.1, p.2.1.2⟩ :
        {p : Ideal (fourVariablePolynomialRing k) |
          p.IsPrime ∧ coordinateVarietyIdeal k ≤ p})).1 :
            Set (coordinateVariety k)) = _
      exact g_apply _
    have hrange : {s : Set (coordinateVariety k) |
        Maximal (fun x => IsClosed x ∧ IsIrreducible x) s} =
        Set.range (fun p : (coordinateVarietyIdeal k).minimalPrimes =>
          (OrderDual.ofDual (hcomp p).1 : Set (coordinateVariety k))) := by
      ext C
      constructor
      · intro hC
        let p := hcomp.symm ⟨C, hC⟩
        refine ⟨p, ?_⟩
        exact congrArg (fun z => (OrderDual.ofDual z.1 : Set (coordinateVariety k)))
          (hcomp.apply_symm_apply ⟨C, hC⟩)
      · rintro ⟨p, hpC⟩
        rw [← hpC]
        exact (hcomp p).2
    rw [hrange]
    change Set.range (fun p : (coordinateVarietyIdeal k).minimalPrimes =>
        (OrderDual.ofDual (hcomp p).1 : Set (coordinateVariety k))) =
      ({coordinateXComponent k, coordinateYZWComponent k} :
        Set (Set (coordinateVariety k)))
    ext C
    constructor
    · rintro ⟨p, rfl⟩
      have hp : p.1 = coordinateXIdeal k ∨ p.1 = coordinateYZWIdeal k := by
        have hp' : p.1 ∈ ({coordinateXIdeal k, coordinateYZWIdeal k} :
            Set (Ideal (fourVariablePolynomialRing k))) := hmin ▸ p.2
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp'
      rcases hp with hp | hp
      · change (OrderDual.ofDual (hcomp p) : Set (coordinateVariety k)) ∈
          ({coordinateXComponent k, coordinateYZWComponent k} :
            Set (Set (coordinateVariety k)))
        rw [hcomp_apply, hp]
        exact Set.mem_insert_iff.mpr (Or.inl rfl)
      · change (OrderDual.ofDual (hcomp p) : Set (coordinateVariety k)) ∈
          ({coordinateXComponent k, coordinateYZWComponent k} :
            Set (Set (coordinateVariety k)))
        rw [hcomp_apply, hp]
        exact Set.mem_insert_iff.mpr (Or.inr rfl)
    · intro hC
      have hC' : C = coordinateXComponent k ∨ C = coordinateYZWComponent k := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hC
      rcases hC' with rfl | rfl
      · have hx : coordinateXIdeal k ∈ (coordinateVarietyIdeal k).minimalPrimes := hXmin
        refine ⟨⟨coordinateXIdeal k, hx⟩, ?_⟩
        simpa [coordinateXComponent, PrimeSpectrum.mem_zeroLocus] using
          (hcomp_apply ⟨coordinateXIdeal k, hx⟩)
      · have hy : coordinateYZWIdeal k ∈ (coordinateVarietyIdeal k).minimalPrimes := hYmin
        refine ⟨⟨coordinateYZWIdeal k, hy⟩, ?_⟩
        simpa [coordinateYZWComponent, PrimeSpectrum.mem_zeroLocus] using
          (hcomp_apply ⟨coordinateYZWIdeal k, hy⟩)
  · constructor
    · let sX : Finset (Fin 4) := {0}
      have hXset : coordinateXIdeal k =
          Ideal.span (MvPolynomial.X '' (sX : Set (Fin 4))) := by
        dsimp [sX, coordinateXIdeal]
        congr 1
        ext z
        simp
      have eX0 := quotient_span_X_finset_ringEquiv (R := k) sX
      have eX : (fourVariablePolynomialRing k ⧸ coordinateXIdeal k) ≃+*
          MvPolynomial {i : Fin 4 // i ∉ sX} k := by
        rw [hXset]
        exact eX0
      rw [ringKrullDim_eq_of_ringEquiv eX,
        MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
      norm_num [sX]
    · let sY : Finset (Fin 4) := {1, 2, 3}
      have hYset : coordinateYZWIdeal k =
          Ideal.span (MvPolynomial.X '' (sY : Set (Fin 4))) := by
        dsimp [sY, coordinateYZWIdeal]
        congr 1
        ext z
        constructor
        · intro hz
          rcases (by simpa using hz) with rfl | rfl | rfl
          · exact ⟨1, by simp, rfl⟩
          · exact ⟨2, by simp, rfl⟩
          · exact ⟨3, by simp, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases (by simpa using hi) with rfl | rfl | rfl <;> simp
      have eY0 := quotient_span_X_finset_ringEquiv (R := k) sY
      have eY : (fourVariablePolynomialRing k ⧸ coordinateYZWIdeal k) ≃+*
          MvPolynomial {i : Fin 4 // i ∉ sY} k := by
        rw [hYset]
        exact eY0
      rw [ringKrullDim_eq_of_ringEquiv eY,
        MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field]
      have hcard : Fintype.card {i : Fin 4 // i ∉ sY} = 1 := by
        decide
      rw [Nat.card_eq_fintype_card, hcard]
      norm_num

end

end Formalization.Books.Exercises.Unit57
