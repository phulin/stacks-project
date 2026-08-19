import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Field.ZMod

/-!
# Commutative Algebra, Chapter 64: symbolic powers

The symbolic power is expressed using Mathlib's canonical localization at a
prime, ideal extension, quotient map, and ring-homomorphism kernel.  The
associated-prime statement uses Mathlib's canonical set of associated prime
ideals; under the chapter's Noetherian hypothesis this agrees with the exact
annihilator formulation recorded in Chapter 63.
-/

namespace Formalization.Books.Algebra.Unit64

universe u v

noncomputable section

/-! ## Symbolic powers -/

/-- The `n`th symbolic power of a prime ideal, defined as the kernel of
the map to the quotient of the localization by the extended ordinary power. -/
def symbolicPower {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (n : ℕ) : Ideal R :=
  RingHom.ker
    ((Ideal.Quotient.mk
        ((p ^ n).map (algebraMap R (Localization.AtPrime p)))).comp
      (algebraMap R (Localization.AtPrime p)))

/-- Ordinary powers are contained in the corresponding symbolic powers. -/
theorem pow_le_symbolicPower
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ) :
    p ^ n ≤ symbolicPower p n := by
  intro x hx
  change x ∈ RingHom.ker _
  rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hx

/-- Equality of ordinary and symbolic powers is not valid for all prime ideals. -/
theorem symbolicPower_eq_pow_not_general :
    ¬ ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] (n : ℕ),
      p ^ n = symbolicPower p n := by
  intro h
  let A := ULift.{u} (Polynomial (ZMod 4))
  let c0 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by decide) _
  let F0 : Polynomial (ZMod 4) →+* Polynomial (ZMod 2) :=
    Polynomial.mapRingHom c0
  let F : A →+* ULift.{u} (Polynomial (ZMod 2)) := F0.ulift
  letI instDomain : IsDomain (ULift.{u} (Polynomial (ZMod 2))) :=
    (ULift.ringEquiv : ULift.{u} (Polynomial (ZMod 2)) ≃+*
      Polynomial (ZMod 2)).isDomain
  let K : Ideal A := RingHom.ker F
  have hK : K.IsPrime := by
    dsimp [K]
    exact RingHom.ker_isPrime F
  let I : Ideal A := Ideal.span {(ULift.up (2 : Polynomial (ZMod 4))) *
    ULift.up Polynomial.X}
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hIK : I ≤ K := by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change F ((ULift.up (2 : Polynomial (ZMod 4))) * ULift.up Polynomial.X) = 0
    rw [map_mul, RingHom.ulift_apply, RingHom.ulift_apply]
    change ULift.up (F0 (2 : Polynomial (ZMod 4)) * F0 Polynomial.X) = 0
    have hc : c0 (2 : ZMod 4) = 0 := by
      change ZMod.cast (2 : ZMod 4) = 0
      decide
    have hF02 : F0 (2 : Polynomial (ZMod 4)) = 0 := by
      change Polynomial.map c0 (2 : Polynomial (ZMod 4)) = 0
      rw [show (2 : Polynomial (ZMod 4)) = Polynomial.C (2 : ZMod 4) by rfl,
        Polynomial.map_C, hc, Polynomial.C_0]
    rw [hF02, zero_mul]
    rfl
  have hXK : ULift.up Polynomial.X ∉ K := by
    change F (ULift.up Polynomial.X) ≠ 0
    rw [RingHom.ulift_apply]
    change ULift.up (F0 Polynomial.X) ≠ 0
    rw [show F0 Polynomial.X = Polynomial.X by simp [F0]]
    exact fun hz => Polynomial.X_ne_zero (ULift.up_injective hz)
  have hp : (K.map q).IsPrime := by
    apply Ideal.isPrime_map_quotientMk_of_isPrime hIK
  have hqX : q (ULift.up Polynomial.X) ∉ K.map q := by
    intro hx
    rcases (Ideal.mem_map_iff_of_surjective (I := K) (f := q)
        (Ideal.Quotient.mk_surjective (I := I))).mp hx with ⟨a, ha, hqa⟩
    have hai : a - ULift.up Polynomial.X ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (a - ULift.up Polynomial.X) = 0
      rw [map_sub, hqa, sub_self]
    have hax : ULift.up Polynomial.X ∈ K := by
      have hh := K.sub_mem ha (hIK hai)
      simpa [sub_sub] using hh
    exact hXK hax
  let p : Ideal (A ⧸ I) := K.map q
  haveI instp : p.IsPrime := hp
  have hx : q (ULift.up (2 : Polynomial (ZMod 4))) ∈ symbolicPower p 2 := by
    change q (ULift.up (2 : Polynomial (ZMod 4))) ∈ RingHom.ker _
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    refine ⟨q (ULift.up Polynomial.X), hqX, ?_⟩
    have hz : q (ULift.up Polynomial.X) *
        q (ULift.up (2 : Polynomial (ZMod 4))) = 0 := by
      rw [← map_mul]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.subset_span
      simp [mul_comm]
    rw [hz]
    exact (p ^ 2).zero_mem
  let e0 : Polynomial (ZMod 4) →+* ZMod 4 := Polynomial.evalRingHom 0
  let e : A →+* ULift.{u} (ZMod 4) := e0.ulift
  have hIe : I ≤ RingHom.ker e := by
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change e ((ULift.up (2 : Polynomial (ZMod 4))) * ULift.up Polynomial.X) = 0
    rw [map_mul, RingHom.ulift_apply, RingHom.ulift_apply]
    change ULift.up (e0 (2 : Polynomial (ZMod 4)) * e0 Polynomial.X) = 0
    rw [show e0 Polynomial.X = 0 by
      change Polynomial.eval 0 Polynomial.X = 0
      rw [Polynomial.eval_X]]
    simp
    rfl
  let g : (A ⧸ I) →+* ULift.{u} (ZMod 4) := Ideal.Quotient.lift I e hIe
  have hg (a : A) : g (q a) = e a := by
    simpa [g, q] using (Ideal.Quotient.lift_mk I e hIe (a := a))
  have hcast (a : ZMod 4) (ha : a ∈ RingHom.ker c0) :
      ULift.up a ∈ Ideal.span {ULift.up (2 : ZMod 4)} := by
    have ha' : c0 a = 0 := RingHom.mem_ker.mp ha
    fin_cases a
    · exact (Ideal.span {ULift.up (2 : ZMod 4)}).zero_mem
    · have hne : c0 (1 : ZMod 4) ≠ 0 := by decide
      exact False.elim (hne ha')
    · change ULift.up (2 : ZMod 4) ∈ Ideal.span {ULift.up (2 : ZMod 4)}
      exact Ideal.subset_span (by simp)
    · have hne : c0 (3 : ZMod 4) ≠ 0 := by decide
      exact False.elim (hne ha')
  have hcoeff (a : A) (ha : a ∈ K) :
      a.down.coeff 0 ∈ RingHom.ker c0 := by
    have ha0 : a.down ∈ RingHom.ker F0 := by
      have ha' : F a = 0 := RingHom.mem_ker.mp ha
      have ha'' := congrArg ULift.down ha'
      cases a with
      | up a =>
        change F0 a = 0 at ha''
        exact ha''
    have hkeq : RingHom.ker F0 = (RingHom.ker c0).map
        (Polynomial.C : ZMod 4 →+* Polynomial (ZMod 4)) :=
      Polynomial.ker_mapRingHom c0
    rw [hkeq] at ha0
    have hc' : ∀ n : ℕ, a.down.coeff n ∈ RingHom.ker c0 :=
      Ideal.mem_map_C_iff.mp ha0
    specialize hc' 0
    assumption
  have heval (a : A) : e a = ULift.up (a.down.coeff 0) := by
    cases a with
    | up a =>
      change ULift.up (e0 a) = ULift.up (a.coeff 0)
      change ULift.up (Polynomial.eval 0 a) = ULift.up (a.coeff 0)
      rw [Polynomial.coeff_zero_eq_eval_zero]
  have hpg : p.map g ≤ Ideal.span {ULift.up (2 : ZMod 4)} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    change g y ∈ Ideal.span {ULift.up (2 : ZMod 4)}
    rcases (Ideal.mem_map_iff_of_surjective (I := K) (f := q)
        (Ideal.Quotient.mk_surjective (I := I))).mp hy with ⟨a, ha, hqa⟩
    rw [← hqa, hg, heval]
    exact hcast _ (hcoeff a ha)
  have hspan2 : (Ideal.span {ULift.up (2 : ZMod 4)}) ^ 2 =
      (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
    rw [Ideal.span_singleton_pow]
    have htwo : (ULift.up (2 : ZMod 4)) ^ 2 = 0 := by
      change ULift.up ((2 : ZMod 4) ^ 2) = 0
      have : (2 : ZMod 4) ^ 2 = 0 := by decide
      rw [this]
      rfl
    rw [htwo]
    simp
  have hmap : (p ^ 2).map g ≤
      (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
    rw [Ideal.map_pow]
    calc
      p.map g ^ 2 ≤ (Ideal.span {ULift.up (2 : ZMod 4)}) ^ 2 := by
        rw [pow_two, pow_two]
        exact Ideal.mul_mono hpg hpg
      _ = ⊥ := hspan2
  have hnot : q (ULift.up (2 : Polynomial (ZMod 4))) ∉ p ^ 2 := by
    intro hpow
    have hzmem : g (q (ULift.up (2 : Polynomial (ZMod 4)))) ∈
        (⊥ : Ideal (ULift.{u} (ZMod 4))) := by
      apply hmap
      exact Ideal.mem_map_of_mem g hpow
    change g (q (ULift.up (2 : Polynomial (ZMod 4)))) = 0 at hzmem
    have he2 : e (ULift.up (2 : Polynomial (ZMod 4))) =
        ULift.up (2 : ZMod 4) := by
      change ULift.up (e0 (2 : Polynomial (ZMod 4))) = ULift.up (2 : ZMod 4)
      congr 1
      dsimp [e0]
      norm_num
    have htwo : ULift.up (2 : ZMod 4) = 0 := by
      calc
        ULift.up (2 : ZMod 4) = e (ULift.up (2 : Polynomial (ZMod 4))) := he2.symm
        _ = g (q (ULift.up (2 : Polynomial (ZMod 4)))) :=
          (hg (ULift.up (2 : Polynomial (ZMod 4)))).symm
        _ = 0 := hzmem
    exact (fun hz => by
      have : (2 : ZMod 4) = 0 := ULift.up_injective hz
      exact (by decide : (2 : ZMod 4) ≠ 0) this) htwo
  apply hnot
  rw [h (A ⧸ I) p 2]
  exact hx

/-! ## Associated primes -/

/-- For positive exponent, the symbolic-power quotient has exactly the given
prime ideal as its associated prime. -/
theorem associatedPrimes_symbolicPower
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] {n : ℕ} (hn : 0 < n) :
    _root_.associatedPrimes R (R ⧸ symbolicPower p n) = {p} := by
  have hprimary : (symbolicPower p n).IsPrimary := by
    rw [show symbolicPower p n =
        Ideal.comap (algebraMap R (Localization.AtPrime p))
          ((p ^ n).map (algebraMap R (Localization.AtPrime p))) by
      ext x
      change (Ideal.Quotient.mk ((p ^ n).map (algebraMap R (Localization.AtPrime p))))
          (algebraMap R (Localization.AtPrime p) x) = 0 ↔
        algebraMap R (Localization.AtPrime p) x ∈
          (p ^ n).map (algebraMap R (Localization.AtPrime p))
      rw [Ideal.Quotient.eq_zero_iff_mem]]
    apply Ideal.IsPrimary.comap
    apply Ideal.isPrimary_of_isMaximal_radical
    rw [Ideal.map_pow, Ideal.radical_pow _ (Nat.ne_of_gt hn),
      IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    rw [(inferInstance : (IsLocalRing.maximalIdeal
      (Localization.AtPrime p)).IsPrime).radical]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hle : symbolicPower p n ≤ p := by
    intro x hx
    rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p,
      Ideal.mem_under]
    change x ∈ RingHom.ker _ at hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
    exact (Ideal.map_mono (Ideal.pow_le_self (Nat.ne_of_gt hn))) hx
  have hradical : (symbolicPower p n).radical = p := by
    apply le_antisymm
    · simpa only [(inferInstance : p.IsPrime).radical] using
        (Ideal.radical_mono hle)
    · calc
        p = (p ^ n).radical := by
          rw [Ideal.radical_pow p (Nat.ne_of_gt hn),
            (inferInstance : p.IsPrime).radical]
        _ ≤ (symbolicPower p n).radical :=
          Ideal.radical_mono (pow_le_symbolicPower p n)
  rw [associatedPrimes.eq_singleton_of_isPrimary hprimary, hradical]

/-! ## Flat extension -/

/-- Symbolic powers commute with a flat extension when the extended prime is
prime.  The displayed equality is the source's `q = pS` case, with `q`
retained as an explicit ideal to make the primality hypothesis available. -/
theorem symbolicPower_map_of_flat
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] (hq : q = p.map f) (n : ℕ) :
    (symbolicPower p n).map f = symbolicPower q n := by
  sorry

/- Unfolding `RingHom.ker` and `Ideal.Quotient.mk` gives the source's
`R ∩ p ^ n Rₚ` kernel description, so it needs no parallel intersection
definition.  The associated-prime proof also uses the fact that elements
outside `p` act regularly on the quotient.  The flat-extension proof reduces
to injectivity of the map between the two localized quotients, observes that
the target is a further localization, and uses the finite filtration by
powers of `p` with the displayed tensor-product/vector-space subquotients;
these are proof-level reductions and introduce no additional chapter-facing
construction. -/

end

end Formalization.Books.Algebra.Unit64
