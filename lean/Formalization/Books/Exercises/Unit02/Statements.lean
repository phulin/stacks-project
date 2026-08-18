import Formalization.Books.Exercises.Unit02.Core

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Exercises, Chapter 2: Colimits

This file records the theorem interfaces for the exercises in the source
section.  Proposition proofs are intentionally deferred to the proving stage
unless Mathlib already supplies the exact result.
-/

noncomputable section

universe u v w

open CategoryTheory
open CategoryTheory.Limits

namespace Formalization.Books.Exercises.Unit02

/-! ## Directed colimits of rings -/

/-- The canonical ring colimit has the universal property stated in the first
exercise. -/
theorem ringColimit_universal
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (_hI : IsDirectedSet I)
    {B : Type w} [CommRing B] (ψ : ∀ i, A i →+* B)
    (hψ : ∀ i j (hij : i ≤ j) (x : A i),
      ψ j (φ i j hij x) = ψ i x) :
    ∃! g : ringColimit φ →+* B,
      ∀ i, g.comp (ringColimitMap φ i) = ψ i := by
  refine ⟨ringColimitLift φ ψ hψ, ?_, ?_⟩
  · intro i
    exact RingHom.ext fun x => ringColimitLift_map φ ψ hψ i x
  · intro g hg
    apply Ring.DirectLimit.hom_ext
    intro i
    apply RingHom.ext
    intro x
    change g (ringColimitMap φ i x) =
      ringColimitLift φ ψ hψ (ringColimitMap φ i x)
    calc
      g (ringColimitMap φ i x) = ψ i x := DFunLike.congr_fun (hg i) x
      _ = ringColimitLift φ ψ hψ (ringColimitMap φ i x) :=
        (ringColimitLift_map φ ψ hψ i x).symm

/-! ## Prime spectra -/

/-- The prime spectrum of a directed ring colimit is in bijection with the
compatible families of primes in its stages. -/
theorem primeSpectrum_colimit_bijective
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (hI : IsDirectedSet I) :
    Function.Bijective (primeSpectrumColimitMap φ) := by
  classical
  rcases hI with ⟨hI0, hId⟩
  let _ : Nonempty I := hI0
  let _ : IsDirectedOrder I := hId
  constructor
  · intro p q hpq
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    constructor <;> intro hx
    · obtain ⟨i, y, rfl⟩ := Ring.DirectLimit.exists_of x
      have hi := congrArg (fun r => (r.1 i).asIdeal) hpq
      have hx' : y ∈ (PrimeSpectrum.comap (ringColimitMap φ i) p).asIdeal := hx
      change y ∈ (PrimeSpectrum.comap (ringColimitMap φ i) q).asIdeal
      exact hi ▸ hx'
    · obtain ⟨i, y, rfl⟩ := Ring.DirectLimit.exists_of x
      have hi := congrArg (fun r => (r.1 i).asIdeal) hpq
      have hx' : y ∈ (PrimeSpectrum.comap (ringColimitMap φ i) q).asIdeal := hx
      change y ∈ (PrimeSpectrum.comap (ringColimitMap φ i) p).asIdeal
      exact hi.symm ▸ hx'
  · rintro ⟨p, hp⟩
    have hpush : ∀ i j (hij : i ≤ j) (x : A i),
        x ∈ (p i).asIdeal → φ i j hij x ∈ (p j).asIdeal := by
      intro i j hij x hx
      have hx' : x ∈ (p j).asIdeal.comap (φ i j hij) := by
        rw [← hp i j hij]
        exact hx
      exact hx'
    let P : Ideal (ringColimit φ) :=
      { carrier := {x | ∃ i y, ringColimitMap φ i y = x ∧ y ∈ (p i).asIdeal}
        zero_mem' := by
          obtain ⟨i⟩ := hI0
          exact ⟨i, 0, map_zero _, (p i).asIdeal.zero_mem⟩
        add_mem' := by
          rintro x y ⟨i, a, hax, ha⟩ ⟨j, b, hby, hb⟩
          obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
          refine ⟨k, φ i k hik a + φ j k hjk b, ?_, ?_⟩
          · rw [map_add, ringColimitMap_compatibility φ hik,
              ringColimitMap_compatibility φ hjk, hax, hby]
          · exact (p k).asIdeal.add_mem (hpush i k hik a ha) (hpush j k hjk b hb)
        smul_mem' := by
          rintro z x ⟨i, a, hax, ha⟩
          obtain ⟨j, b, hzb⟩ := Ring.DirectLimit.exists_of z
          change ringColimitMap φ j b = z at hzb
          obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
          refine ⟨k, φ j k hjk b * φ i k hik a, ?_, ?_⟩
          · calc
              ringColimitMap φ k (φ j k hjk b * φ i k hik a) =
                  ringColimitMap φ j b * ringColimitMap φ i a := by
                    rw [map_mul, ringColimitMap_compatibility φ hjk,
                      ringColimitMap_compatibility φ hik]
              _ = z * x := by rw [hzb, hax]
              _ = z • x := by rw [smul_eq_mul]
          · exact (p k).asIdeal.mul_mem_left _ (hpush i k hik a ha) }
    have hPprime : P.IsPrime := by
      rw [Ideal.isPrime_iff]
      constructor
      · intro htop
        have h1 : (1 : ringColimit φ) ∈ P := by rw [htop]; simp
        change ∃ i y, ringColimitMap φ i y = 1 ∧ y ∈ (p i).asIdeal at h1
        obtain ⟨j, y, hy, hyp⟩ := h1
        have hz : ringColimitMap φ j (y - 1) = 0 := by
          rw [map_sub, hy, map_one, sub_self]
        obtain ⟨k, hjk, hzero⟩ := Ring.DirectLimit.of.zero_exact hz
        rw [map_sub, map_one] at hzero
        have hyk : φ j k hjk y = 1 := sub_eq_zero.mp hzero
        have hmem := hpush j k hjk y hyp
        rw [hyk] at hmem
        exact (p k).2.ne_top ((Ideal.eq_top_iff_one _).mpr hmem)
      · intro x y hxy
        change ∃ i c, ringColimitMap φ i c = x * y ∧ c ∈ (p i).asIdeal at hxy
        obtain ⟨i, c, hc, hcp⟩ := hxy
        obtain ⟨j, a, hax⟩ := Ring.DirectLimit.exists_of x
        obtain ⟨k, b, hby⟩ := Ring.DirectLimit.exists_of y
        change ringColimitMap φ j a = x at hax
        change ringColimitMap φ k b = y at hby
        obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
        obtain ⟨m, hlm, him⟩ := exists_ge_ge l i
        have hprod : ringColimitMap φ l
            (φ j l hjl a * φ k l hkl b) = x * y := by
          rw [map_mul, ringColimitMap_compatibility φ hjl,
            ringColimitMap_compatibility φ hkl, hax, hby]
        have hzero : ringColimitMap φ m
            (φ l m hlm (φ j l hjl a * φ k l hkl b) -
              φ i m him c) = 0 := by
          rw [map_sub, ringColimitMap_compatibility φ hlm,
            ringColimitMap_compatibility φ him, hprod, hc, sub_self]
        obtain ⟨n, hmn, hzero_n⟩ := Ring.DirectLimit.of.zero_exact hzero
        rw [map_sub] at hzero_n
        have hcmem : φ m n hmn (φ i m him c) ∈ (p n).asIdeal :=
          hpush m n hmn _ (hpush i m him c hcp)
        have hprodmem : φ m n hmn
            (φ l m hlm (φ j l hjl a * φ k l hkl b)) ∈ (p n).asIdeal := by
          rw [sub_eq_zero.mp hzero_n]
          exact hcmem
        have hprodmem' : (φ m n hmn (φ l m hlm (φ j l hjl a * φ k l hkl b))) ∈
            (p n).asIdeal := hprodmem
        rw [map_mul, map_mul] at hprodmem'
        rcases (p n).2.mul_mem_iff_mem_or_mem.mp hprodmem' with ha_n | hb_n
        · left
          refine ⟨n, φ m n hmn (φ l m hlm (φ j l hjl a)), ?_, ha_n⟩
          calc
            ringColimitMap φ n (φ m n hmn (φ l m hlm (φ j l hjl a))) =
                ringColimitMap φ m (φ l m hlm (φ j l hjl a)) :=
              ringColimitMap_compatibility φ hmn _
            _ = ringColimitMap φ l (φ j l hjl a) :=
              ringColimitMap_compatibility φ hlm _
            _ = ringColimitMap φ j a :=
              ringColimitMap_compatibility φ hjl _
            _ = x := hax
        · right
          refine ⟨n, φ m n hmn (φ l m hlm (φ k l hkl b)), ?_, hb_n⟩
          calc
            ringColimitMap φ n (φ m n hmn (φ l m hlm (φ k l hkl b))) =
                ringColimitMap φ m (φ l m hlm (φ k l hkl b)) :=
              ringColimitMap_compatibility φ hmn _
            _ = ringColimitMap φ l (φ k l hkl b) :=
              ringColimitMap_compatibility φ hlm _
            _ = ringColimitMap φ k b :=
              ringColimitMap_compatibility φ hkl _
            _ = y := hby
    refine ⟨⟨P, hPprime⟩, ?_⟩
    apply Subtype.ext
    apply funext
    intro i
    apply PrimeSpectrum.ext
    apply Ideal.ext
    intro x
    constructor
    · intro hx
      change ∃ j y, ringColimitMap φ j y = ringColimitMap φ i x ∧ y ∈ (p j).asIdeal at hx
      obtain ⟨j, y, hy, hyp⟩ := hx
      obtain ⟨l, hjl, hil⟩ := exists_ge_ge j i
      have hz : ringColimitMap φ l
          (φ j l hjl y - φ i l hil x) = 0 := by
        rw [map_sub, ringColimitMap_compatibility φ hjl,
          ringColimitMap_compatibility φ hil, hy, sub_self]
      obtain ⟨m, hlm, hzero⟩ := Ring.DirectLimit.of.zero_exact hz
      rw [map_sub] at hzero
      have hmem : φ l m hlm (φ j l hjl y) ∈ (p m).asIdeal :=
        hpush l m hlm _ (hpush j l hjl y hyp)
      have hmem' : φ l m hlm (φ i l hil x) ∈ (p m).asIdeal := by
        rw [← sub_eq_zero.mp hzero]
        exact hmem
      have hmem'' : φ i m (hil.trans hlm) x ∈ (p m).asIdeal := by
        simpa only [DirectedSystem.map_map'] using hmem'
      have hx' : x ∈ (p m).asIdeal.comap (φ i m (hil.trans hlm)) := hmem''
      rw [← hp i m (hil.trans hlm)] at hx'
      exact hx'
    · intro hx
      exact ⟨i, x, rfl, hx⟩

/-- If every transition map induces a surjection on prime spectra, then each
stage maps surjectively to the spectrum of the directed colimit. -/
theorem primeSpectrum_colimit_map_surjective_of_stagewise
    {I : Type u} [Preorder I]
    {A : I → Type v} [∀ i, CommRing (A i)]
    (φ : RingSystem I A) [DirectedSystem A (φ · · ·)]
    (hI : IsDirectedSet I)
    (hSpec : ∀ i j (hij : i ≤ j),
      Function.Surjective (PrimeSpectrum.comap (φ i j hij))) :
    ∀ i, Function.Surjective (PrimeSpectrum.comap (ringColimitMap φ i)) := by
  classical
  rcases hI with ⟨hI0, hId⟩
  let _ : Nonempty I := hI0
  let _ : IsDirectedOrder I := hId
  intro i p
  let Q : ringColimit φ → Prop :=
    fun z => ∃ (j : I) (hij : i ≤ j) (y : A j),
      ringColimitMap φ j y = z ∧ y ∈ Ideal.map (φ i j hij) p.asIdeal
  have hcomp : ∀ (r s t : I) (hrs : r ≤ s) (hst : s ≤ t),
      (φ s t hst).comp (φ r s hrs) = φ r t (hrs.trans hst) := by
    intro r s t hrs hst
    apply RingHom.ext
    intro x
    exact DirectedSystem.map_map' (φ · · ·) hrs hst x
  have hQ : ∀ z, z ∈ Ideal.map (ringColimitMap φ i) p.asIdeal → Q z := by
    intro z hz
    change z ∈ Ideal.span ((ringColimitMap φ i) '' (p.asIdeal : Set (A i))) at hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · rintro z ⟨a, ha, rfl⟩
      refine ⟨i, le_rfl, a, rfl, ?_⟩
      simpa only [DirectedSystem.map_self'] using
        (Ideal.mem_map_of_mem (φ i i le_rfl) ha)
    · exact ⟨i, le_rfl, 0, map_zero _, (Ideal.map (φ i i le_rfl) p.asIdeal).zero_mem⟩
    · rintro x y _ _ ⟨j, hij, a, hxa, ha⟩ ⟨k, hik, b, hxb, hb⟩
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
      refine ⟨l, hij.trans hjl, φ j l hjl a + φ k l hkl b, ?_, ?_⟩
      · rw [map_add, ringColimitMap_compatibility φ hjl,
          ringColimitMap_compatibility φ hkl, hxa, hxb]
      · apply (Ideal.map (φ i l (hij.trans hjl)) p.asIdeal).add_mem
        · have hm := Ideal.mem_map_of_mem (φ j l hjl) ha
          rw [Ideal.map_map, hcomp i j l hij hjl] at hm
          exact hm
        · have hm := Ideal.mem_map_of_mem (φ k l hkl) hb
          rw [Ideal.map_map, hcomp i k l hik hkl] at hm
          exact hm
    · rintro z x _ ⟨j, hij, a, hzx, ha⟩
      obtain ⟨k, b, hzb⟩ := Ring.DirectLimit.exists_of z
      change ringColimitMap φ k b = z at hzb
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
      refine ⟨l, hij.trans hjl, φ k l hkl b * φ j l hjl a, ?_, ?_⟩
      · calc
          ringColimitMap φ l (φ k l hkl b * φ j l hjl a) =
              ringColimitMap φ k b * ringColimitMap φ j a := by
                rw [map_mul, ringColimitMap_compatibility φ hkl,
                  ringColimitMap_compatibility φ hjl]
          _ = z • x := by rw [hzb, hzx, smul_eq_mul]
      · exact (Ideal.map (φ i l (hij.trans hjl)) p.asIdeal).mul_mem_left _ <|
          by
            have hm := Ideal.mem_map_of_mem (φ j l hjl) ha
            rw [Ideal.map_map, hcomp i j l hij hjl] at hm
            exact hm
  have hmap_push : ∀ (j : I) (hij : i ≤ j) (k : I) (hjk : j ≤ k) (y : A j),
      y ∈ Ideal.map (φ i j hij) p.asIdeal →
        φ j k hjk y ∈ Ideal.map (φ i k (hij.trans hjk)) p.asIdeal := by
    intro j hij k hjk y hy
    have hm := Ideal.mem_map_of_mem (φ j k hjk) hy
    rw [Ideal.map_map, hcomp i j k hij hjk] at hm
    exact hm
  have hcomap :
      (Ideal.map (ringColimitMap φ i) p.asIdeal).comap (ringColimitMap φ i) =
        p.asIdeal := by
    apply le_antisymm
    · intro x hx
      change ringColimitMap φ i x ∈ Ideal.map (ringColimitMap φ i) p.asIdeal at hx
      obtain ⟨j, hij, y, hy, hyp⟩ := hQ _ hx
      obtain ⟨l, hjl, hil⟩ := exists_ge_ge j i
      have hz : ringColimitMap φ l
          (φ j l hjl y - φ i l hil x) = 0 := by
        rw [map_sub, ringColimitMap_compatibility φ hjl,
          ringColimitMap_compatibility φ hil, hy, sub_self]
      obtain ⟨m, hlm, hzero⟩ := Ring.DirectLimit.of.zero_exact hz
      rw [map_sub] at hzero
      have hmem := hmap_push j hij l hjl y hyp
      have hmem' := hmap_push l (hij.trans hjl) m hlm _ hmem
      have him : i ≤ m := (hij.trans hjl).trans hlm
      let q := Classical.choose (hSpec i m him p)
      have hq := Classical.choose_spec (hSpec i m him p)
      have hqideal : q.asIdeal.comap (φ i m him) = p.asIdeal := by
        simpa [q] using congrArg PrimeSpectrum.asIdeal hq
      have hle : Ideal.map (φ i m him) p.asIdeal ≤ q.asIdeal := by
        rw [Ideal.map_le_iff_le_comap, ← hqideal]
      have hmem_q : φ l m hlm (φ j l hjl y) ∈ q.asIdeal := hle hmem'
      have hmem_x : φ l m hlm (φ i l hil x) ∈ q.asIdeal := by
        rw [← sub_eq_zero.mp hzero]
        exact hmem_q
      have hmem_x' : φ i m (hil.trans hlm) x ∈ q.asIdeal := by
        simpa only [DirectedSystem.map_map'] using hmem_x
      have hx' : x ∈ q.asIdeal.comap (φ i m him) := hmem_x'
      rw [hqideal] at hx'
      exact hx'
    · exact Ideal.le_comap_map
  let _ : p.asIdeal.IsPrime := p.2
  obtain ⟨q, hq, hqeq⟩ :=
    (Ideal.comap_map_eq_self_iff_of_isPrime (f := ringColimitMap φ i) p.asIdeal).mp hcomap
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqeq⟩

/-! ## Integral extensions -/

/-- Every finite subalgebra in an integral extension is finite as a module over
the base ring. -/
theorem finiteSubalgebra_finite_of_integral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (s : Finset B) :
    Module.Finite A (finiteSubalgebra (A := A) (B := B) s) := by
  exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)

/-- The finite subalgebras generated inside `B` have colimit `B`. -/
theorem finiteSubalgebra_colimit_bijective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    Function.Bijective (finiteSubalgebraColimitMap (A := A) (B := B)) := by
  classical
  constructor
  · unfold finiteSubalgebraColimitMap
    apply Ring.DirectLimit.lift_injective
    intro s
    exact Subtype.val_injective
  · intro b
    let s : Finset B := {b}
    let x : finiteSubalgebra (A := A) (B := B) s :=
      ⟨b, Algebra.subset_adjoin (by simp [s])⟩
    refine ⟨Ring.DirectLimit.of _ _ s x, ?_⟩
    unfold finiteSubalgebraColimitMap
    simp [x]

/-- An integral injective ring map induces a surjection on prime spectra. -/
theorem integral_extension_primeSpectrum_surjective
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (hIntegral : f.IsIntegral) :
    Function.Surjective (PrimeSpectrum.comap f) := by
  exact hIntegral.comap_surjective hf

/-! ## Tensor products -/

/- The displayed tensor-product isomorphism is the real definition
`tensorProductDirectedColimitEquiv`, whose body is Mathlib's canonical
`TensorProduct.directLimitRight` equivalence. -/

/-! ## Finite presentation -/

/-- A source-facing characterization of finite presentation by a cokernel of a
map between finite free modules. -/
theorem finitePresentation_iff_finite_free_cokernel
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Module.FinitePresentation R M ↔
      ∃ n m : ℕ,
        ∃ f : ModuleCat.of R (Fin n → R) ⟶ ModuleCat.of R (Fin m → R),
          Nonempty (ModuleCat.of R M ≅ cokernel f) := by
  sorry

/-! ## Colimits of modules -/

/-- Every module is the directed colimit of its finitely generated
submodules.  The equivalence is Mathlib's canonical `Module.fgSystem.equiv`. -/
theorem module_is_colimit_of_finitely_generated_submodules
    {R M : Type u} [Semiring R] [AddCommMonoid M] [Module R M] :
    Nonempty
      (letI : DecidableEq (Submodule R M) := Classical.decEq _
       Module.DirectLimit
          (fun N : {N : Submodule R M // N.FG} => N)
          (Module.fgSystem R M) ≃ₗ[R] M) := by
  let h : DecidableEq (Submodule R M) := Classical.decEq _
  exact ⟨@Module.fgSystem.equiv R M _ _ _ h⟩

/-- Every module admits a directed-colimit presentation by finitely presented
modules. -/
theorem exists_directed_finitelyPresented_module_colimit
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M] :
    Nonempty
      (DirectedFinitelyPresentedModuleColimit (ModuleCat.of R M)) := by
  sorry

end Formalization.Books.Exercises.Unit02
