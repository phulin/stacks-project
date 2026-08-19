import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit68.RegularSequences
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.ReesAlgebra

/-!
# Commutative Algebra, Chapter 69: Quasi-regular sequences

The associated graded pieces are written as nested submodule quotients.  For an ideal `I`,
the denominator in degree `n` is `I • ⊤` inside `I ^ n • ⊤`; this is the canonical Mathlib
presentation of `I ^ n M / I ^ (n + 1) M`.
-/

namespace Formalization.Books.Algebra.Unit69

open scoped DirectSum Pointwise TensorProduct

noncomputable section

universe u v

/-! ## The canonical graded map -/

/-- The total degree of a finitely supported multi-index. -/
def quasiRegularDegree {n : ℕ} (d : Fin n →₀ ℕ) : ℕ :=
  d.sum fun _ e => e

/-- The coefficient in `R` attached to a multi-index and a finite sequence. -/
def quasiRegularMonomialCoefficient
    {R : Type u} [CommRing R] (f : List R) (d : Fin f.length →₀ ℕ) : R :=
  d.prod fun i e => f.get i ^ e

/-- Each monomial coefficient belongs to the corresponding power of the generated ideal. -/
theorem quasiRegularMonomialCoefficient_mem
    {R : Type u} [CommRing R] (f : List R) (d : Fin f.length →₀ ℕ) :
    quasiRegularMonomialCoefficient f d ∈
      (Ideal.ofList f) ^ quasiRegularDegree d := by
  sorry

/-- The `n`-th associated graded piece of a module for an ideal. -/
abbrev quasiRegularPiece
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) :=
  (↥(I ^ n • (⊤ : Submodule R M))) ⧸
    (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))))

/-- The direct sum of the associated graded pieces. -/
abbrev quasiRegularTarget
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :=
  ⨁ n, quasiRegularPiece R M I n

/-! ## The associated graded ring and adic lifting -/

/-- The coefficientwise next-power ideal in the Rees algebra.  Its quotient is the
associated graded ring: in degree `n` it kills precisely `I ^ (n + 1)`. -/
def adicAssociatedGradedKernel
    {R : Type u} [CommRing R] (I : Ideal R) : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, p.1.coeff n ∈ I ^ (n + 1)}
  zero_mem' n := by simp
  add_mem' {p q} hp hq n := by
    simpa using Ideal.add_mem (I ^ (n + 1)) (hp n) (hq n)
  smul_mem' p q hq n := by
    change (p.1 * q.1).coeff n ∈ I ^ (n + 1)
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨i, j⟩ hij
    have hp : p.1.coeff i ∈ I ^ i := p.2 i
    have hmul : p.1.coeff i * q.1.coeff j ∈ I ^ i * I ^ (j + 1) :=
      Ideal.mul_mem_mul hp (hq j)
    rw [← Ideal.IsTwoSided.pow_add] at hmul
    have hn : i + j = n := Finset.mem_antidiagonal.mp hij
    rw [show i + (j + 1) = n + 1 by omega] at hmul
    exact hmul

/-- The associated graded ring `gr_I(R)`, presented as the Rees algebra modulo the
coefficientwise next-power ideal. -/
abbrev adicAssociatedGradedRing
    {R : Type u} [CommRing R] (I : Ideal R) :=
  reesAlgebra I ⧸ adicAssociatedGradedKernel I

/-- The homogeneous form of `x ∈ I^n` in degree `n` of the associated graded ring. -/
def adicAssociatedGradedForm
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) (x : R) (hx : x ∈ I ^ n) :
    adicAssociatedGradedRing I :=
  Ideal.Quotient.mk (adicAssociatedGradedKernel I)
    ⟨Polynomial.monomial n x, reesAlgebra.monomial_mem.mpr hx⟩

@[simp]
theorem adicAssociatedGradedForm_zero
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    adicAssociatedGradedForm I n 0 (Ideal.zero_mem _) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro k
  simp

private theorem adicAssociatedGraded_algebraMap_mem_kernel
    {R : Type u} [CommRing R] (I : Ideal R) (x : R) (hx : x ∈ I) :
    algebraMap R (reesAlgebra I) x ∈ adicAssociatedGradedKernel I := by
  intro n
  change (Polynomial.C x).coeff n ∈ I ^ (n + 1)
  rw [Polynomial.coeff_C]
  split_ifs with hn
  · subst n
    simpa using hx
  · exact Ideal.zero_mem _

/-- If `I` is finitely generated and `R / I` is Noetherian, then `gr_I(R)` is
Noetherian.  In particular this applies to every ideal in a Noetherian ring. -/
theorem adicAssociatedGradedRing_isNoetherian
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    [IsNoetherianRing (R ⧸ I)] :
    IsNoetherianRing (adicAssociatedGradedRing I) := by
  let K := adicAssociatedGradedKernel I
  let G := adicAssociatedGradedRing I
  let : Algebra.FiniteType R (reesAlgebra I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  let q : R →+* G :=
    (Ideal.Quotient.mk K).comp (algebraMap R (reesAlgebra I))
  have hIq : I ≤ RingHom.ker q := by
    intro x hx
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk K (algebraMap R (reesAlgebra I) x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact adicAssociatedGraded_algebraMap_mem_kernel I x hx
  let qI : R ⧸ I →+* G := Ideal.Quotient.lift I q hIq
  let : Algebra (R ⧸ I) G := qI.toAlgebra' fun _ _ =>
    @mul_comm G (Ideal.Quotient.commSemiring K).toCommMagma _ _
  let : IsScalarTower R (R ⧸ I) G :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change Ideal.Quotient.mk K (algebraMap R (reesAlgebra I) x) =
        Ideal.Quotient.mk K (algebraMap R (reesAlgebra I) x)
      rfl
  have : Algebra.FiniteType R G := Algebra.FiniteType.quotient R K
  have : Algebra.FiniteType (R ⧸ I) G :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ I) G
  exact Algebra.FiniteType.isNoetherianRing (R ⧸ I) G

/-- A finite family of elements of `J`, tagged by their adic degrees, generates all
initial forms when every element of `J ∩ I^n` can be reduced modulo `I^(n+1)` by
coefficients of the complementary degrees. -/
def AdicHomogeneousGenerators
    {R : Type u} [CommRing R] (I J : Ideal R) (s : Finset (ℕ × R)) : Prop :=
  (∀ a ∈ s, a.2 ∈ J ∧ a.2 ∈ I ^ a.1) ∧
    ∀ (n : ℕ) (y : R), y ∈ J → y ∈ I ^ n →
      ∃ c : s → R,
        (∀ a, c a ∈ I ^ (n - a.1.1)) ∧
          y - ∑ a, c a * a.1.2 ∈ I ^ (n + 1)

/-- Homogeneous generators lift to ordinary ideal generators in an adically complete
ring.  This is the completeness step in the graded criterion for Noetherianity. -/
theorem isNoetherianRing_of_isAdicComplete_of_homogeneous_generators
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (hhom : ∀ J : Ideal R, ∃ s : Finset (ℕ × R),
      AdicHomogeneousGenerators I J s) :
    IsNoetherianRing R := by
  classical
  apply (isNoetherianRing_iff_ideal_fg R).mpr
  intro J
  obtain ⟨s, hs⟩ := hhom J
  refine Submodule.fg_def.mpr
    ⟨(↑(s.image Prod.snd) : Set R), Finset.finite_toSet _, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact (hs.1 a ha).1
  · intro y hy
    let C : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} → (s → R) :=
      fun n r => Classical.choose (hs.2 n r r.2.1 r.2.2)
    have C_mem (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}) (a : s) :
        C n r a ∈ I ^ (n - a.1.1) :=
      (Classical.choose_spec (hs.2 n r r.2.1 r.2.2)).1 a
    have C_remainder (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}) :
        r.1 - ∑ a : s, C n r a * a.1.2 ∈ I ^ (n + 1) :=
      (Classical.choose_spec (hs.2 n r r.2.1 r.2.2)).2
    let next (n : ℕ) (r : {r : R // r ∈ J ∧ r ∈ I ^ n}) :
        {r : R // r ∈ J ∧ r ∈ I ^ (n + 1)} :=
      ⟨r.1 - ∑ a : s, C n r a * a.1.2,
        ⟨J.sub_mem r.2.1 (J.sum_mem fun a _ =>
            J.mul_mem_left (C n r a) (hs.1 a a.2).1),
          C_remainder n r⟩⟩
    let z : (n : ℕ) → {r : R // r ∈ J ∧ r ∈ I ^ n} :=
      fun n => Nat.rec (motive := fun n => {r : R // r ∈ J ∧ r ∈ I ^ n})
        ⟨y, hy, by simp⟩ (fun n r => next n r) n
    let c (n : ℕ) : s → R := C n (z n)
    let psum (n : ℕ) (a : s) : R := ∑ k ∈ Finset.range n, c k a
    have c_mem (n : ℕ) (a : s) : c n a ∈ I ^ (n - a.1.1) := by
      exact C_mem n (z n) a
    have z_zero : (z 0).1 = y := rfl
    have z_succ (n : ℕ) :
        (z (n + 1)).1 = (z n).1 - ∑ a : s, c n a * a.1.2 := by
      rfl
    have telescopes (n : ℕ) :
        y - ∑ a : s, psum n a * a.1.2 = (z n).1 := by
      induction n with
      | zero => simp [psum, z_zero]
      | succ n hn =>
          calc
            y - ∑ a : s, psum (n + 1) a * a.1.2 =
                (y - ∑ a : s, psum n a * a.1.2) -
                  ∑ a : s, c n a * a.1.2 := by
                    simp only [psum, Finset.sum_range_succ, add_mul,
                      Finset.sum_add_distrib]
                    abel
            _ = (z n).1 - ∑ a : s, c n a * a.1.2 := by rw [hn]
            _ = (z (n + 1)).1 := (z_succ n).symm
    have psum_add (m n : ℕ) (a : s) :
        psum (m + n) a = psum m a + ∑ k ∈ Finset.range n, c (m + k) a := by
      simp [psum, Finset.sum_range_add]
    have psum_cauchy (a : s) :
        ∀ {m n : ℕ}, m ≤ n →
          psum (m + a.1.1) a ≡ psum (n + a.1.1) a
            [SMOD (I ^ m • (⊤ : Submodule R R))] := by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
      let l := n - m
      have hn : n = m + l := (Nat.add_sub_of_le hmn).symm
      rw [hn, show (m + l) + a.1.1 = (m + a.1.1) + l by omega,
        psum_add (m + a.1.1) l a]
      rw [sub_add_eq_sub_sub, sub_self, zero_sub]
      apply neg_mem
      apply Ideal.sum_mem
      intro k hk
      apply Ideal.pow_le_pow_right (show m ≤ (m + a.1.1 + k) - a.1.1 by omega)
      exact c_mem (m + a.1.1 + k) a
    choose b hb using fun a : s =>
      IsPrecomplete.prec (inferInstance : IsPrecomplete I R) (psum_cauchy a)
    have hy_eq : y = ∑ a : s, b a * a.1.2 := by
      rw [← sub_eq_zero]
      apply IsHausdorff.haus (inferInstance : IsHausdorff I R)
      intro k
      rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
      let D := s.sup fun a => a.1
      let N := k + D
      have hkN : k ≤ N := Nat.le_add_right k D
      have hres : y - ∑ a : s, psum N a * a.1.2 ∈ I ^ N := by
        rw [telescopes]
        exact (z N).2.2
      have hcoeff (a : s) : (psum N a - b a) * a.1.2 ∈ I ^ N := by
        have haD : a.1.1 ≤ D := Finset.le_sup a.2
        have haN : a.1.1 ≤ N := haD.trans (Nat.le_add_left D k)
        have hab : psum N a - b a ∈ I ^ (N - a.1.1) := by
          have h := hb a (N - a.1.1)
          rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
          simpa [Nat.sub_add_cancel haN] using h
        have hmul : (psum N a - b a) * a.1.2 ∈
            I ^ (N - a.1.1) * I ^ a.1.1 :=
          Ideal.mul_mem_mul hab (hs.1 a.1 a.2).2
        rw [← Ideal.IsTwoSided.pow_add, Nat.sub_add_cancel haN] at hmul
        exact hmul
      have hsum : ∑ a : s, (psum N a - b a) * a.1.2 ∈ I ^ N :=
        Ideal.sum_mem _ fun a _ => hcoeff a
      apply Ideal.pow_le_pow_right hkN
      have hadd := Ideal.add_mem (I ^ N) hres hsum
      convert hadd using 1
      simp only [sub_mul, Finset.sum_sub_distrib]
      abel
    rw [hy_eq]
    apply Submodule.sum_mem
    intro a _
    simpa only [smul_eq_mul] using
      Submodule.smul_mem (Submodule.span R (↑(s.image Prod.snd) : Set R)) (b a)
        (Submodule.subset_span (by
          exact Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩))

/-- Homogeneous forms of elements of `J`, in all adic degrees. -/
def adicAssociatedGradedInitialForms
    {R : Type u} [CommRing R] (I J : Ideal R) :
    Set (adicAssociatedGradedRing I) :=
  {g | ∃ (n : ℕ) (x : R) (_hxJ : x ∈ J) (hxI : x ∈ I ^ n),
    g = adicAssociatedGradedForm I n x hxI}

private theorem exists_finset_subset_span_eq_of_fg
    {A : Type*} [CommRing A] (S : Set A) (h : (Ideal.span S).FG) :
    ∃ t : Finset A, (↑t : Set A) ⊆ S ∧
      Submodule.span A (↑t : Set A) = (Ideal.span S : Submodule A A) := by
  classical
  obtain ⟨U, hUfin, hUspan⟩ := Submodule.fg_def.mp h
  let u := hUfin.toFinset
  have hu : (↑u : Set A) ⊆ Submodule.span A S := by
    intro x hx
    rw [hUfin.coe_toFinset] at hx
    change x ∈ (Ideal.span S : Ideal A)
    rw [← hUspan]
    exact Submodule.subset_span hx
  obtain ⟨t, htS, hut⟩ := Submodule.subset_span_finite_of_subset_span hu
  refine ⟨t, htS, le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.mpr (htS.trans Submodule.subset_span)
  · rw [← hUspan]
    apply Submodule.span_le.mpr
    intro x hx
    apply hut
    simpa [u, hUfin.coe_toFinset] using hx

/-- Noetherianity of the associated graded ring supplies a finite homogeneous
reduction family for every ideal. -/
theorem exists_adicHomogeneousGenerators_of_isNoetherian_associatedGraded
    {R : Type u} [CommRing R] (I J : Ideal R)
    [IsNoetherianRing (adicAssociatedGradedRing I)] :
    ∃ s : Finset (ℕ × R), AdicHomogeneousGenerators I J s := by
  classical
  let G := adicAssociatedGradedRing I
  let K := adicAssociatedGradedKernel I
  let S := adicAssociatedGradedInitialForms I J
  have hfg : (Ideal.span S).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨t, htS, htspan⟩ := exists_finset_subset_span_eq_of_fg S hfg
  choose d x hxJ hxI hform using fun a : t => htS a.2
  let pair : t → ℕ × R := fun a => (d a, x a)
  have pair_injective : Function.Injective pair := by
    intro a b hab
    apply Subtype.ext
    have hd : d a = d b := congrArg Prod.fst hab
    have hx : x a = x b := congrArg Prod.snd hab
    rw [hform a, hform b]
    apply congrArg (Ideal.Quotient.mk (adicAssociatedGradedKernel I))
    apply Subtype.ext
    dsimp only [adicAssociatedGradedForm]
    rw [hd, hx]
  let s : Finset (ℕ × R) := t.attach.image pair
  let toData : t → s := fun a =>
    ⟨pair a, Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩⟩
  have toData_injective : Function.Injective toData := fun a b h =>
    pair_injective (congrArg Subtype.val h)
  have toData_surjective : Function.Surjective toData := by
    intro a
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp a.2
    exact ⟨b, Subtype.ext hb⟩
  let e : t ≃ s := Equiv.ofBijective toData ⟨toData_injective, toData_surjective⟩
  refine ⟨s, ?_, ?_⟩
  · intro a ha
    let b := e.symm ⟨a, ha⟩
    have hpair : pair b = a := congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
    exact ⟨hpair ▸ hxJ b, hpair ▸ hxI b⟩
  · intro n y hyJ hyI
    have hyS : adicAssociatedGradedForm I n y hyI ∈ S :=
      ⟨n, y, hyJ, hyI, rfl⟩
    have hyspan : adicAssociatedGradedForm I n y hyI ∈
        Submodule.span G (↑t : Set G) := by
      rw [htspan]
      exact Ideal.subset_span hyS
    obtain ⟨a, ha⟩ := Submodule.mem_span_finset'.mp hyspan
    choose q hq using fun b : t =>
      Ideal.Quotient.mk_surjective (a b)
    let monomial (b : t) : reesAlgebra I :=
      ⟨Polynomial.monomial (d b) (x b), reesAlgebra.monomial_mem.mpr (hxI b)⟩
    have hquot :
        Ideal.Quotient.mk K
            ⟨Polynomial.monomial n y, reesAlgebra.monomial_mem.mpr hyI⟩ =
          Ideal.Quotient.mk K (∑ b : t, q b * monomial b) := by
      rw [map_sum]
      change adicAssociatedGradedForm I n y hyI =
        ∑ b : t, Ideal.Quotient.mk K (q b) * Ideal.Quotient.mk K (monomial b)
      rw [← ha]
      apply Finset.sum_congr rfl
      intro b _
      simp only [smul_eq_mul]
      rw [← hq b, hform b]
      rfl
    have hker :
        ⟨Polynomial.monomial n y, reesAlgebra.monomial_mem.mpr hyI⟩ -
            ∑ b : t, q b * monomial b ∈ K :=
      Ideal.Quotient.eq.mp hquot
    have coeff_mul_monomial (b : t) :
        ((q b).1 * (monomial b).1).coeff n =
          if d b ≤ n then (q b).1.coeff (n - d b) * x b else 0 := by
      split_ifs with hdn
      · change ((q b).1 * Polynomial.monomial (d b) (x b)).coeff n = _
        calc
          ((q b).1 * Polynomial.monomial (d b) (x b)).coeff n =
              ((q b).1 * Polynomial.monomial (d b) (x b)).coeff
                ((n - d b) + d b) := by rw [Nat.sub_add_cancel hdn]
          _ = (q b).1.coeff (n - d b) * x b :=
            Polynomial.coeff_mul_monomial (q b).1 (d b) (n - d b) (x b)
      · have hnlt : n < d b := Nat.lt_of_not_ge hdn
        rw [show (monomial b).1 = Polynomial.monomial (d b) (x b) by rfl,
          ← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc,
          Polynomial.coeff_mul_X_pow', if_neg hdn]
    let ct (b : t) : R :=
      if d b ≤ n then (q b).1.coeff (n - d b) else 0
    have ct_mem (b : t) : ct b ∈ I ^ (n - d b) := by
      dsimp [ct]
      split_ifs with hdn
      · exact (q b).2 (n - d b)
      · exact Ideal.zero_mem _
    have hremainder : y - ∑ b : t, ct b * x b ∈ I ^ (n + 1) := by
      have h := hker n
      simp only [Subalgebra.coe_sub] at h
      rw [Polynomial.coeff_sub, Polynomial.coeff_monomial_same] at h
      have hsum_coe :
          (↑(∑ b : t, q b * monomial b) : Polynomial R) =
            ∑ b : t, (Subalgebra.val (reesAlgebra I)) (q b) *
              (Subalgebra.val (reesAlgebra I)) (monomial b) := by
        change (Subalgebra.val (reesAlgebra I)) (∑ b : t, q b * monomial b) = _
        exact
          (map_sum (Subalgebra.val (reesAlgebra I))
            (fun b : t => q b * monomial b) Finset.univ)
      rw [hsum_coe] at h
      have hcoeff_sum :
          (∑ b : t, (Subalgebra.val (reesAlgebra I)) (q b) *
              (Subalgebra.val (reesAlgebra I)) (monomial b)).coeff n =
            ∑ b : t, ((Subalgebra.val (reesAlgebra I)) (q b) *
              (Subalgebra.val (reesAlgebra I)) (monomial b)).coeff n := by
        simpa only [Polynomial.lcoeff_apply] using
          (map_sum (Polynomial.lcoeff R n)
            (fun b : t => (Subalgebra.val (reesAlgebra I)) (q b) *
              (Subalgebra.val (reesAlgebra I)) (monomial b)) Finset.univ)
      rw [hcoeff_sum] at h
      convert h using 1
      apply congrArg (fun z : R => y - z)
      apply Finset.sum_congr rfl
      intro b _
      dsimp [ct]
      split_ifs with hdn
      · simpa [hdn] using (coeff_mul_monomial b).symm
      · simpa [hdn] using (coeff_mul_monomial b).symm
    refine ⟨fun z => ct (e.symm z), ?_, ?_⟩
    · intro z
      have hp : pair (e.symm z) = z.1 :=
        congrArg Subtype.val (e.apply_symm_apply z)
      have hd : d (e.symm z) = z.1.1 := congrArg Prod.fst hp
      simpa only [hd] using ct_mem (e.symm z)
    · have hsum :
          ∑ z : s, ct (e.symm z) * z.1.2 = ∑ b : t, ct b * x b := by
        calc
          ∑ z : s, ct (e.symm z) * z.1.2 =
              ∑ b : t, ct (e.symm (e b)) * (e b).1.2 :=
            (e.sum_comp (fun z : s => ct (e.symm z) * z.1.2)).symm
          _ = ∑ b : t, ct b * x b := by
            apply Finset.sum_congr rfl
            intro b _
            simp only [e.symm_apply_apply]
            rfl
      simpa only [hsum] using hremainder

/-- If a ring is adically complete and its associated graded ring is Noetherian,
then the ring itself is Noetherian. -/
theorem isNoetherianRing_of_isAdicComplete_of_associatedGraded
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    [IsNoetherianRing (adicAssociatedGradedRing I)] :
    IsNoetherianRing R := by
  apply isNoetherianRing_of_isAdicComplete_of_homogeneous_generators I
  intro J
  exact exists_adicHomogeneousGenerators_of_isNoetherian_associatedGraded I J

/-- A finitely generated ideal with Noetherian quotient in an adically complete ring
has a Noetherian ambient ring. -/
theorem isNoetherianRing_of_isAdicComplete_of_fg_quotient
    {R : Type u} [CommRing R] (I : Ideal R) [IsNoetherianRing (R ⧸ I)]
    [IsAdicComplete I R] (hI : I.FG) :
    IsNoetherianRing R := by
  let : IsNoetherianRing (adicAssociatedGradedRing I) :=
    adicAssociatedGradedRing_isNoetherian I hI
  exact isNoetherianRing_of_isAdicComplete_of_associatedGraded I

/-- The associated graded ring of an ideal in a Noetherian ring is Noetherian. -/
theorem adicAssociatedGradedRing_isNoetherian_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (adicAssociatedGradedRing I) := by
  exact adicAssociatedGradedRing_isNoetherian I I.fg_of_isNoetherianRing

/-- The source of the canonical graded map in the textbook. -/
abbrev quasiRegularSource
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :=
  (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) ⊗[R ⧸ Ideal.ofList f]
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f)

/-- The raw map sending a module element to the corresponding monomial in one graded piece. -/
def quasiRegularMonomialMapRaw
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    M →ₗ[R] quasiRegularPiece R M (Ideal.ofList f) (quasiRegularDegree d) := by
  let I := Ideal.ofList f
  let n := quasiRegularDegree d
  let P := I ^ n • (⊤ : Submodule R M)
  let Q := I • (⊤ : Submodule R ↥P)
  let a := quasiRegularMonomialCoefficient f d
  let ha : a ∈ I ^ n := quasiRegularMonomialCoefficient_mem f d
  let φ : M →ₗ[R] ↥P :=
    (LinearMap.lsmul R M a).codRestrict P (fun m =>
      Submodule.smul_mem_smul ha (Submodule.mem_top : m ∈ (⊤ : Submodule R M)))
  exact Q.mkQ.comp φ

/-- Multiplication by an element of the generated ideal kills the raw monomial map. -/
theorem quasiRegularMonomialMapRaw_ker
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    Ideal.ofList f • (⊤ : Submodule R M) ≤
      LinearMap.ker (quasiRegularMonomialMapRaw R M f d) := by
  sorry

/-- The raw map is semilinear for the quotient map on scalars. -/
theorem quasiRegularMonomialMapRaw_map_smul_quotient
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (r : R) (m : M) :
    quasiRegularMonomialMapRaw R M f d (r • m) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularMonomialMapRaw R M f d m := by
  sorry

/- The quotient of a semilinear map by `I` is linear over `R ⧸ I`. -/
theorem quotientSemilinearMap_smul
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R)
    (hN : Module.IsTorsionBySet R N I)
    (g : letI := hN.module
      (M ⧸ (I • (⊤ : Submodule R M))) →ₛₗ[Ideal.Quotient.mk I] N)
    (s : R ⧸ I) (x : M ⧸ (I • (⊤ : Submodule R M))) :
    let := hN.module
    g (s • x) = s • g x := by
  sorry

/-- Turn the semilinear quotient map into its canonical quotient-ring linear map. -/
def quotientSemilinearMapToLinear
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (I : Ideal R)
    (hN : Module.IsTorsionBySet R N I)
    (g : letI := hN.module
      (M ⧸ (I • (⊤ : Submodule R M))) →ₛₗ[Ideal.Quotient.mk I] N) :
    letI := hN.module
    (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] N :=
  letI := hN.module
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun s x => quotientSemilinearMap_smul I hN g s x }

/-- The monomial map after passing to `M / IM`. -/
def quasiRegularMonomialMapQuotient
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularPiece R M (Ideal.ofList f) (quasiRegularDegree d) := by
  let I := Ideal.ofList f
  let hN := Module.isTorsionBySet_quotient_ideal_smul
    (M := ↥(I ^ quasiRegularDegree d • (⊤ : Submodule R M))) (I := I)
  letI : Module (R ⧸ I)
      (quasiRegularPiece R M I (quasiRegularDegree d)) := hN.module
  let g : M →ₛₗ[Ideal.Quotient.mk I]
      quasiRegularPiece R M I (quasiRegularDegree d) :=
    { toFun := quasiRegularMonomialMapRaw R M f d
      map_add' := (quasiRegularMonomialMapRaw R M f d).map_add
      map_smul' := fun r m => quasiRegularMonomialMapRaw_map_smul_quotient R M f d r m }
  let gq := (I • (⊤ : Submodule R M)).liftQ g
    (quasiRegularMonomialMapRaw_ker R M f d)
  exact quotientSemilinearMapToLinear I hN gq

theorem quasiRegularMonomialMapQuotient_mk
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (m : M) :
    quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk
        (⟨quasiRegularMonomialCoefficient f d • m,
          Submodule.smul_mem_smul (quasiRegularMonomialCoefficient_mem f d)
            (show m ∈ (⊤ : Submodule R M) from trivial)⟩ :
          ↥((Ideal.ofList f) ^ quasiRegularDegree d •
            (⊤ : Submodule R M))) := by
  rfl

/-- Coefficients from the arbitrary module act on every associated-graded piece through `R / I`. -/
theorem quasiRegularMonomialMapQuotient_coeff_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (r : R) (m : M) :
    quasiRegularMonomialMapQuotient R M f d
        (Submodule.Quotient.mk (r • m)) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m) := by
  sorry

/-- The polynomial-linear map obtained by summing the monomial components. -/
def quasiRegularPolynomialMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (m : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  (Finsupp.lsum (R ⧸ Ideal.ofList f) (fun d =>
      LinearMap.toSpanSingleton (R ⧸ Ideal.ofList f)
        (quasiRegularTarget R M (Ideal.ofList f))
        (DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
          (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
          (quasiRegularDegree d)
          (quasiRegularMonomialMapQuotient R M f d m)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (R ⧸ Ideal.ofList f)).toLinearMap

theorem quasiRegularPolynomialMap_add
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (m₁ m₂ : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularPolynomialMap R M f (m₁ + m₂) =
      quasiRegularPolynomialMap R M f m₁ + quasiRegularPolynomialMap R M f m₂ := by
  sorry

theorem quasiRegularPolynomialMap_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (c : R ⧸ Ideal.ofList f)
    (m : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularPolynomialMap R M f (c • m) =
      c • quasiRegularPolynomialMap R M f m := by
  sorry

/-- The bilinear map underlying the canonical tensor-product map. -/
def quasiRegularBilinearMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) →ₗ[R ⧸ Ideal.ofList f]
      MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) →ₗ[R ⧸ Ideal.ofList f]
        quasiRegularTarget R M (Ideal.ofList f) :=
  LinearMap.mk₂ (R ⧸ Ideal.ofList f)
    (fun m p => quasiRegularPolynomialMap R M f m p)
    (fun m₁ m₂ p => by
      simpa using congrArg (fun q => q p) (quasiRegularPolynomialMap_add R M f m₁ m₂))
    (fun c m p => by
      simpa using congrArg (fun q => q p) (quasiRegularPolynomialMap_smul R M f c m))
    (fun m p₁ p₂ => (quasiRegularPolynomialMap R M f m).map_add p₁ p₂)
    (fun c m p => (quasiRegularPolynomialMap R M f m).map_smul c p)

/-- The canonical graded map from the textbook. -/
def quasiRegularCanonicalMap
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    quasiRegularSource R M f →ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  TensorProduct.lift (quasiRegularBilinearMap R M f)

private theorem range_lTensor_idealPower_smul_top
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module.Flat R S]
    (I : Ideal R) (n : ℕ) :
    LinearMap.range
        (TensorProduct.AlgebraTensorModule.lTensor S S
          (I ^ n • (⊤ : Submodule R M)).subtype) =
      (I.map (algebraMap R S)) ^ n •
        (⊤ : Submodule S (S ⊗[R] M)) := by
  rw [← Ideal.map_pow]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa using add_mem hx hy
    | tmul s x =>
        change s ⊗ₜ[R] (x : M) ∈
          (I ^ n).map (algebraMap R S) •
            (⊤ : Submodule S (S ⊗[R] M))
        refine Submodule.smul_induction_on x.property ?_ ?_
        · intro r hr m _
          rw [TensorProduct.tmul_smul]
          simpa [Algebra.smul_def] using
            Submodule.smul_mem_smul
              (Ideal.mem_map_of_mem (algebraMap R S) hr)
              (show s ⊗ₜ[R] m ∈ (⊤ : Submodule S (S ⊗[R] M)) from trivial)
        · intro x y hx hy
          rw [TensorProduct.tmul_add]
          exact add_mem hx hy
  · intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha z _
      rw [Ideal.map] at ha
      refine Submodule.span_induction (p := fun a : S => fun _ =>
          ∀ z : S ⊗[R] M,
            a • z ∈ LinearMap.range
              (TensorProduct.AlgebraTensorModule.lTensor S S
                (I ^ n • (⊤ : Submodule R M)).subtype))
        ?_ ?_ ?_ ?_ ha z
      · rintro _ ⟨r, hr, rfl⟩ z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy =>
            rw [smul_add]
            exact add_mem hx hy
        | tmul s m =>
            refine ⟨s ⊗ₜ[R]
              (⟨r • m, Submodule.smul_mem_smul hr trivial⟩ :
                ↥(I ^ n • (⊤ : Submodule R M))), ?_⟩
            simp
      · intro z
        simp
      · intro a b _ _ ha hb z
        rw [add_smul]
        exact add_mem (ha z) (hb z)
      · intro a b _ hb z
        simpa [smul_smul] using
          (LinearMap.range
            (TensorProduct.AlgebraTensorModule.lTensor S S
              (I ^ n • (⊤ : Submodule R M)).subtype)).smul_mem a (hb z)
    · intro x y hx hy
      exact add_mem hx hy

theorem quasiRegularTensorQuotMapEquiv_symm_tmul_mk
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    (I : Ideal R) (s : S) (m : M) :
    (TensorProduct.tensorQuotMapSMulEquivTensorQuot M S I).symm
        (s ⊗ₜ[R] Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (s ⊗ₜ[R] m) := by
  have hq :
      (Ideal.qoutMapEquivTensorQout (I := I) S).symm
          (s ⊗ₜ[R] (1 : R ⧸ I)) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) s := by
    unfold Ideal.qoutMapEquivTensorQout
    change
      ((TensorProduct.tensorQuotEquivQuotSMul S I ≪≫ₗ
          Submodule.quotEquivOfEq _ _ _ ≪≫ₗ
          Submodule.Quotient.restrictScalarsEquiv R _) (s ⊗ₜ[R] 1)) = _
    simp only [LinearEquiv.trans_apply]
    rw [show (1 : R ⧸ I) = Ideal.Quotient.mk I 1 by rfl,
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    simp
  simp [TensorProduct.tensorQuotMapSMulEquivTensorQuot, hq]
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  change s • (1 ⊗ₜ[R] m) = s ⊗ₜ[R] m
  rw [TensorProduct.smul_tmul']
  simp

/-- Flat base change identifies each quotient in the ideal-power filtration with the
corresponding quotient for the extended ideal. -/
noncomputable def quasiRegularPieceBaseChangeEquiv
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    (hflat : RingHom.Flat (algebraMap R S)) (I : Ideal R) (n : ℕ) :
    S ⊗[R] quasiRegularPiece R M I n ≃ₗ[S]
      quasiRegularPiece S (S ⊗[R] M) (I.map (algebraMap R S)) n := by
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  let P : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let P' : Submodule S (S ⊗[R] M) :=
    (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S (S ⊗[R] M))
  let g : S ⊗[R] P →ₗ[S] S ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.lTensor S S P.subtype
  have hg : Function.Injective g :=
    Module.Flat.lTensor_preserves_injective_linearMap P.subtype Subtype.val_injective
  have hrange : LinearMap.range g = P' := by
    simpa only [P, P', g] using range_lTensor_idealPower_smul_top (S := S) I n
  let eP : S ⊗[R] P ≃ₗ[S] P' :=
    (LinearEquiv.ofInjective g hg).trans
      (LinearEquiv.ofEq (LinearMap.range g) P' hrange)
  let eQ :
      ((S ⊗[R] P) ⧸
          (I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] P)))) ≃ₗ[S]
        quasiRegularPiece S (S ⊗[R] M) (I.map (algebraMap R S)) n :=
    Submodule.Quotient.equiv _ _ eP (by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr eP.surjective])
  exact
    (TensorProduct.tensorQuotMapSMulEquivTensorQuot P S I).symm ≪≫ₗ eQ

theorem quasiRegularPieceBaseChangeEquiv_tmul_mk
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    (hflat : RingHom.Flat (algebraMap R S)) (I : Ideal R) (n : ℕ)
    (s : S) (x : ↥(I ^ n • (⊤ : Submodule R M))) :
    quasiRegularPieceBaseChangeEquiv hflat I n
        (s ⊗ₜ[R] Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (⟨s ⊗ₜ[R] (x : M), by
          let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
          rw [← range_lTensor_idealPower_smul_top (S := S) I n]
          exact ⟨s ⊗ₜ[R] x, rfl⟩⟩ :
          ↥((I.map (algebraMap R S)) ^ n •
            (⊤ : Submodule S (S ⊗[R] M)))) := by
  have hq :
      (Ideal.qoutMapEquivTensorQout (I := I) S).symm
          (s ⊗ₜ[R] (1 : R ⧸ I)) =
        Ideal.Quotient.mk (I.map (algebraMap R S)) s := by
    unfold Ideal.qoutMapEquivTensorQout
    change
      ((TensorProduct.tensorQuotEquivQuotSMul S I ≪≫ₗ
          Submodule.quotEquivOfEq _ _ _ ≪≫ₗ
          Submodule.Quotient.restrictScalarsEquiv R _) (s ⊗ₜ[R] 1)) = _
    simp only [LinearEquiv.trans_apply]
    rw [show (1 : R ⧸ I) = Ideal.Quotient.mk I 1 by rfl,
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
    simp
  simp [quasiRegularPieceBaseChangeEquiv,
    TensorProduct.tensorQuotMapSMulEquivTensorQuot,
    hq, Submodule.mapQ_apply]
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  change s • (1 ⊗ₜ[R] (x : M)) = s ⊗ₜ[R] (x : M)
  rw [TensorProduct.smul_tmul']
  simp

private theorem quasiRegularPiece_cast_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {n' n : ℕ} (h : n' = n) (x : M)
    (hx' : x ∈ I ^ n' • (⊤ : Submodule R M))
    (hx : x ∈ I ^ n • (⊤ : Submodule R M)) :
    (h ▸ (Submodule.Quotient.mk ⟨x, hx'⟩ : quasiRegularPiece R M I n')) =
      (Submodule.Quotient.mk ⟨x, hx⟩ : quasiRegularPiece R M I n) := by
  subst n
  rfl

private theorem directSum_lof_eq_of_cast
    {R R' ι : Type*} [Semiring R] [Semiring R']
    [DecidableEq ι]
    (N : ι → Type*) [∀ i, AddCommMonoid (N i)]
    [∀ i, Module R (N i)] [∀ i, Module R' (N i)]
    {i' i : ι} (h : i' = i) (x : N i) (x' : N i')
    (hx : h ▸ x' = x) :
    DirectSum.lof R ι N i x = DirectSum.lof R' ι N i' x' := by
  subst i
  subst x
  rfl

/-- Monomial coordinates for the source of the quasi-regular canonical map. -/
noncomputable def quasiRegularSourceFinsuppEquiv
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    quasiRegularSource R M f ≃ₗ[R ⧸ Ideal.ofList f]
      ((Fin f.length →₀ ℕ) →₀
        (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M)))) :=
  TensorProduct.equivFinsuppOfBasisRight
    (MvPolynomial.basisMonomials (Fin f.length) (R ⧸ Ideal.ofList f))

theorem quasiRegularSourceFinsuppEquiv_symm_single
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ)
    (x : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    (quasiRegularSourceFinsuppEquiv R M f).symm (Finsupp.single d x) =
      x ⊗ₜ[R ⧸ Ideal.ofList f] MvPolynomial.monomial d 1 := by
  simp [quasiRegularSourceFinsuppEquiv,
    TensorProduct.equivFinsuppOfBasisRight_symm_apply,
    MvPolynomial.coe_basisMonomials]

theorem quasiRegularSourceFinsuppEquiv_tmul_monomial
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ)
    (x : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularSourceFinsuppEquiv R M f
        (x ⊗ₜ[R ⧸ Ideal.ofList f] MvPolynomial.monomial d 1) =
      Finsupp.single d x := by
  apply (quasiRegularSourceFinsuppEquiv R M f).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (quasiRegularSourceFinsuppEquiv_symm_single R M f d x).symm

theorem quasiRegularCanonicalMap_monomial
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (m : M) (d : Fin f.length →₀ ℕ) :
    quasiRegularCanonicalMap R M f
        (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList f]
          MvPolynomial.monomial d 1) =
      DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
        (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
        (quasiRegularDegree d)
        (quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m)) := by
  sorry

theorem quasiRegularCanonicalMap_coeff_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (r : R) (m : M) (d : Fin f.length →₀ ℕ) :
    quasiRegularCanonicalMap R M f
        (Submodule.Quotient.mk (r • m) ⊗ₜ[R ⧸ Ideal.ofList f]
          MvPolynomial.monomial d 1) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularCanonicalMap R M f
          (Submodule.Quotient.mk m ⊗ₜ[R ⧸ Ideal.ofList f]
            MvPolynomial.monomial d 1) := by
  sorry

/-- The canonical graded map is always surjective. -/
theorem quasiRegularCanonicalMap_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    Function.Surjective (quasiRegularCanonicalMap R M f) := by
  sorry

/-! ## Definition and basic properties -/

/-- A sequence is `M`-quasi-regular when the canonical graded map is an isomorphism. -/
def IsMQuasiRegular
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : Prop :=
  Function.Bijective (quasiRegularCanonicalMap R M f)

/-- A sequence is quasi-regular when it is `R`-quasi-regular on the regular module. -/
def IsQuasiRegular
    (R : Type u) [CommRing R] (f : List R) : Prop :=
  IsMQuasiRegular R R f

/-- The isomorphism represented by an `M`-quasi-regular sequence. -/
noncomputable def quasiRegularCanonicalEquiv
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : IsMQuasiRegular R M f) :
    quasiRegularSource R M f ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  LinearEquiv.ofBijective (quasiRegularCanonicalMap R M f) hf

/- The definition is independent of the ordering of the sequence. -/
theorem isMQuasiRegular_iff_of_perm
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : List R} (hfg : f.Perm g) :
    IsMQuasiRegular R M f ↔ IsMQuasiRegular R M g := by
  sorry

/- The regular-sequence comparison from Lemma 69.3. -/
private theorem regular_single_power_coeff_relation
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (ha : IsSMulRegular M a) (m : M)
    (hm : a ^ n • m ∈ a ^ (n + 1) • (⊤ : Submodule R M)) :
    m ∈ a • (⊤ : Submodule R M) := by
  obtain ⟨z, _, hz⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists (a ^ n • m) (a ^ (n + 1))
      (⊤ : Submodule R M)).mp hm
  have hcancel : m = a • z := by
    apply ha.pow n
    change a ^ n • m = a ^ n • (a • z)
    rw [← hz, pow_succ, mul_smul]
  rw [hcancel]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨z, Submodule.mem_top, rfl⟩

private theorem quasiRegularCanonicalMap_finsupp
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (c : (Fin f.length →₀ ℕ) →₀
      (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M)))) :
    quasiRegularCanonicalMap R M f
        ((quasiRegularSourceFinsuppEquiv R M f).symm c) =
      c.sum (fun d m =>
        DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
          (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
          (quasiRegularDegree d)
          (quasiRegularMonomialMapQuotient R M f d m)) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add d m c hd hm ih =>
      rw [LinearEquiv.map_add, map_add, ih]
      rw [Finsupp.sum_add_index] <;> simp
      rw [quasiRegularSourceFinsuppEquiv_symm_single]
      induction m using Submodule.Quotient.induction_on with
      | _ m =>
          rw [quasiRegularCanonicalMap_monomial]

private theorem quasiRegularCanonicalMap_component_finsupp
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R)
    (c : (Fin f.length →₀ ℕ) →₀
      (M ⧸ (Ideal.ofList f • (⊤ : Submodule R M)))) (n : ℕ) :
    (DirectSum.component (R ⧸ Ideal.ofList f) ℕ
        (fun n => quasiRegularPiece R M (Ideal.ofList f) n) n)
        (quasiRegularCanonicalMap R M f
          ((quasiRegularSourceFinsuppEquiv R M f).symm c)) =
      (DirectSum.component (R ⧸ Ideal.ofList f) ℕ
        (fun n => quasiRegularPiece R M (Ideal.ofList f) n) n)
        (∑ d ∈ c.support.filter (fun d => quasiRegularDegree d = n),
          DirectSum.lof (R ⧸ Ideal.ofList f) ℕ
            (fun n => quasiRegularPiece R M (Ideal.ofList f) n)
            (quasiRegularDegree d)
            (quasiRegularMonomialMapQuotient R M f d (c d))) := by
  classical
  rw [quasiRegularCanonicalMap_finsupp, Finsupp.sum]
  rw [map_sum, map_sum]
  symm
  apply Finset.sum_subset
    (Finset.filter_subset (fun d => quasiRegularDegree d = n) c.support)
  · intro d hd hdn
    simp only [DirectSum.component.of]
    split_ifs with h
    · exact False.elim (hdn (Finset.mem_filter.mpr ⟨hd, h⟩))
    · simp

theorem isMQuasiRegular_of_isRegular
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (hf : RingTheory.Sequence.IsRegular M f) :
    IsMQuasiRegular R M f := by
  sorry

theorem isQuasiRegular_of_isRegular
    {R : Type u} [CommRing R] {f : List R}
    (hf : RingTheory.Sequence.IsRegular R f) : IsQuasiRegular R f := by
  exact isMQuasiRegular_of_isRegular hf

/-- In the ring case, quasi-regularity identifies the polynomial ring over the quotient
with the associated graded object. -/
noncomputable def quasiRegular_graded_ring_identification
    {R : Type u} [CommRing R] (f : List R)
    (hf : IsQuasiRegular R f) :
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R R (Ideal.ofList f) := by
  let I := Ideal.ofList f
  let hI : (I • (⊤ : Submodule R R)) = (I : Submodule R R) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  let eQ : (R ⧸ (I • (⊤ : Submodule R R))) ≃ₗ[R ⧸ I] (R ⧸ I) := by
    let eR : (R ⧸ (I • (⊤ : Submodule R R))) ≃ₗ[R] (R ⧸ I) :=
      Submodule.quotEquivOfEq _ _ hI
    exact
      { eR with
        map_smul' := by
          intro c x
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
          induction x using Submodule.Quotient.induction_on with
          | _ x => rfl }
  let eSource : quasiRegularSource R R f ≃ₗ[R ⧸ I]
      MvPolynomial (Fin f.length) (R ⧸ I) :=
    eQ.rTensor (MvPolynomial (Fin f.length) (R ⧸ I)) ≪≫ₗ
      TensorProduct.lid (R ⧸ I) (MvPolynomial (Fin f.length) (R ⧸ I))
  exact eSource.symm ≪≫ₗ quasiRegularCanonicalEquiv R R f hf

/-! ## Base change, localization, and truncation -/

theorem isMQuasiRegular_of_flat_baseChange
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [Algebra R S]
    (hflat : RingHom.Flat (algebraMap R S)) (f : List R)
    (hf : IsMQuasiRegular R M f) :
    IsMQuasiRegular S (S ⊗[R] M) (f.map (algebraMap R S)) := by
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  let I : Ideal R := Ideal.ofList f
  let fS : List S := f.map (algebraMap R S)
  let J : Ideal S := Ideal.ofList fS
  let A := M ⧸ (I • (⊤ : Submodule R M))
  let A' := (S ⊗[R] M) ⧸ (J • (⊤ : Submodule S (S ⊗[R] M)))
  have hJ : J = I.map (algebraMap R S) := by
    simp [I, J, fS, Ideal.map_ofList]
  have hJA :
      J • (⊤ : Submodule S (S ⊗[R] M)) =
        I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M)) :=
    congrArg (fun K : Ideal S => K • (⊤ : Submodule S (S ⊗[R] M))) hJ
  let eA : A' ≃ₗ[S] S ⊗[R] A :=
    (Submodule.quotEquivOfEq _ _ hJA).trans
      (TensorProduct.tensorQuotMapSMulEquivTensorQuot M S I)
  let eFin : Fin f.length ≃ Fin fS.length :=
    finCongr (by simp [fS])
  let eDeg : (Fin f.length →₀ ℕ) ≃ (Fin fS.length →₀ ℕ) :=
    (Finsupp.domCongr eFin).toEquiv
  have eDeg_degree (d : Fin f.length →₀ ℕ) :
      quasiRegularDegree (eDeg d) = quasiRegularDegree d := by
    simp [quasiRegularDegree, eDeg, eFin]
  have eDeg_coefficient (d : Fin f.length →₀ ℕ) :
      quasiRegularMonomialCoefficient fS (eDeg d) =
        algebraMap R S (quasiRegularMonomialCoefficient f d) := by
    simp [quasiRegularMonomialCoefficient, eDeg, eFin, fS]
  let cR := quasiRegularSourceFinsuppEquiv R M f
  let cS := quasiRegularSourceFinsuppEquiv S (S ⊗[R] M) fS
  let eSource : S ⊗[R] quasiRegularSource R M f ≃ₗ[S]
      quasiRegularSource S (S ⊗[R] M) fS :=
    (cR.restrictScalars R).baseChange R S ≪≫ₗ
      TensorProduct.finsuppRight R S S A (Fin f.length →₀ ℕ) ≪≫ₗ
      Finsupp.lcongr eDeg eA.symm ≪≫ₗ
      (cS.restrictScalars S).symm
  let eIdeal (n : ℕ) :
      quasiRegularPiece S (S ⊗[R] M) (I.map (algebraMap R S)) n ≃ₗ[S]
        quasiRegularPiece S (S ⊗[R] M) J n := by
    let P : Submodule S (S ⊗[R] M) :=
      (I.map (algebraMap R S)) ^ n • (⊤ : Submodule S (S ⊗[R] M))
    let P' : Submodule S (S ⊗[R] M) :=
      J ^ n • (⊤ : Submodule S (S ⊗[R] M))
    have hP : P = P' := by
      change (I.map (algebraMap R S)) ^ n •
          (⊤ : Submodule S (S ⊗[R] M)) =
        J ^ n • (⊤ : Submodule S (S ⊗[R] M))
      rw [hJ]
    let eP : P ≃ₗ[S] P' := LinearEquiv.ofEq P P' hP
    exact Submodule.Quotient.equiv _ _ eP (by
      rw [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr eP.surjective, ← hJ])
  let ePiece (n : ℕ) :
      S ⊗[R] quasiRegularPiece R M I n ≃ₗ[S]
        quasiRegularPiece S (S ⊗[R] M) J n :=
    quasiRegularPieceBaseChangeEquiv (M := M) hflat I n ≪≫ₗ eIdeal n
  let eTarget : S ⊗[R] quasiRegularTarget R M I ≃ₗ[S]
      quasiRegularTarget S (S ⊗[R] M) J :=
    TensorProduct.directSumRight R S S
        (fun n => quasiRegularPiece R M I n) ≪≫ₗ
      DirectSum.congrLinearEquiv ePiece
  let u : quasiRegularSource R M f →ₗ[R] quasiRegularTarget R M I :=
    (quasiRegularCanonicalMap R M f).restrictScalars R
  let v : quasiRegularSource S (S ⊗[R] M) fS →ₗ[S]
      quasiRegularTarget S (S ⊗[R] M) J :=
    (quasiRegularCanonicalMap S (S ⊗[R] M) fS).restrictScalars S
  have hcomm :
      eTarget.toLinearMap.comp (u.baseChange S) =
        v.comp eSource.toLinearMap := by
    have heA (t : S) (m : M) :
        eA.symm (t ⊗ₜ[R] Submodule.Quotient.mk m) =
          Submodule.Quotient.mk (t ⊗ₜ[R] m) := by
      simp only [eA, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
      rw [quasiRegularTensorQuotMapEquiv_symm_tmul_mk]
      rfl
    have hePiece_mk (n : ℕ) (t : S)
        (x : ↥(I ^ n • (⊤ : Submodule R M))) :
        ePiece n (t ⊗ₜ[R] Submodule.Quotient.mk x) =
          Submodule.Quotient.mk
            (⟨t ⊗ₜ[R] (x : M), by
              rw [hJ, ← range_lTensor_idealPower_smul_top (S := S) I n]
              exact ⟨t ⊗ₜ[R] x, rfl⟩⟩ :
              ↥(J ^ n • (⊤ : Submodule S (S ⊗[R] M)))) := by
      simp [ePiece, eIdeal, quasiRegularPieceBaseChangeEquiv_tmul_mk,
        Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
      congr 1
    have hlof (t : S) (n : ℕ) (x : quasiRegularPiece R M I n) :
        TensorProduct.directSumRight R S S
            (fun n => quasiRegularPiece R M I n)
            (t ⊗ₜ[R]
              DirectSum.lof (R ⧸ I) ℕ
                (fun n => quasiRegularPiece R M I n) n x) =
          DirectSum.lof S ℕ
            (fun n => S ⊗[R] quasiRegularPiece R M I n) n (t ⊗ₜ[R] x) := by
      change
        TensorProduct.directSumRight R S S
            (fun n => quasiRegularPiece R M I n)
            (t ⊗ₜ[R]
              DirectSum.lof R ℕ
                (fun n => quasiRegularPiece R M I n) n x) = _
      rw [TensorProduct.directSumRight_tmul_lof]
    apply TensorProduct.AlgebraTensorModule.ext
    intro s z
    let b := cR z
    have hz : z = cR.symm b := by
      exact (cR.symm_apply_apply z).symm
    rw [hz]
    clear hz
    clear_value b
    clear z
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
        simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | single d x =>
        induction x using Submodule.Quotient.induction_on with
        | _ m =>
          simp [eTarget, eSource, u, v, cR, cS,
            quasiRegularSourceFinsuppEquiv_symm_single,
            quasiRegularSourceFinsuppEquiv_tmul_monomial,
            quasiRegularCanonicalMap_monomial,
            quasiRegularMonomialMapQuotient_mk,
            DirectSum.coe_congrLinearEquiv, heA, hePiece_mk, hlof,
            eDeg_coefficient, I, J, fS, A, A']
          apply directSum_lof_eq_of_cast
            (N := fun n => quasiRegularPiece S (S ⊗[R] M) J n)
            (eDeg_degree d)
          exact quasiRegularPiece_cast_mk J (eDeg_degree d)
            (quasiRegularMonomialCoefficient f d • s ⊗ₜ[R] m) _ _
  have hu : Function.Bijective u := by
    change Function.Bijective (quasiRegularCanonicalMap R M f)
    exact hf
  have hubc : Function.Bijective (u.baseChange S) := by
    constructor
    · simpa only [LinearMap.baseChange_eq_ltensor] using
        Module.Flat.lTensor_preserves_injective_linearMap u hu.1
    · simpa only [LinearMap.baseChange_eq_ltensor] using
        LinearMap.lTensor_surjective S hu.2
  have hcomm_apply (x : S ⊗[R] quasiRegularSource R M f) :
      eTarget (u.baseChange S x) = v (eSource x) := by
    change eTarget.toLinearMap (u.baseChange S x) = v (eSource.toLinearMap x)
    simpa only [LinearMap.comp_apply] using congrArg (fun g => g x) hcomm
  have hv : Function.Bijective v := by
    constructor
    · intro x y hxy
      apply eSource.symm.injective
      apply hubc.1
      apply eTarget.injective
      calc
        eTarget (u.baseChange S (eSource.symm x)) = v x := by
          simpa using hcomm_apply (eSource.symm x)
        _ = v y := hxy
        _ = eTarget (u.baseChange S (eSource.symm y)) := by
          simpa using (hcomm_apply (eSource.symm y)).symm
    · intro y
      obtain ⟨x, hx⟩ := hubc.2 (eTarget.symm y)
      refine ⟨eSource x, ?_⟩
      calc
        v (eSource x) = eTarget (u.baseChange S x) := (hcomm_apply x).symm
        _ = eTarget (eTarget.symm y) := congrArg eTarget hx
        _ = y := eTarget.apply_symm_apply y
  change Function.Bijective
    (quasiRegularCanonicalMap S (S ⊗[R] M) fS)
  change Function.Bijective
    (quasiRegularCanonicalMap S (S ⊗[R] M) fS) at hv
  exact hv

theorem isMQuasiRegular_in_neighborhood
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (f : List R)
    (hp : IsMQuasiRegular (Localization.AtPrime p)
      (LocalizedModule.AtPrime p M)
      (f.map (algebraMap R (Localization.AtPrime p)))) :
    ∃ g : R, g ∉ p ∧
      IsMQuasiRegular (Localization (Submonoid.powers g))
        (LocalizedModule (Submonoid.powers g) M)
        (f.map (algebraMap R (Localization (Submonoid.powers g)))) := by
  sorry

theorem isMQuasiRegular_tail
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (hf : IsMQuasiRegular R M f) (i : ℕ) :
    IsMQuasiRegular (R ⧸ Ideal.ofList (f.take i))
      (M ⧸ (Ideal.ofList (f.take i) • (⊤ : Submodule R M)))
      ((f.drop i).map (Ideal.Quotient.mk (Ideal.ofList (f.take i)))) := by
  sorry

theorem isMRegular_of_isMQuasiRegular_of_isLocal
    {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Nontrivial M) (f : List R)
    (hf : ∀ x ∈ f, x ∈ IsLocalRing.maximalIdeal R)
    (hq : IsMQuasiRegular R M f) :
    RingTheory.Sequence.IsRegular M f := by
  sorry

/-!
The next source remark defines Koszul-regular and `H₁`-regular sequences using the Koszul
complex and explicitly defers their detailed construction and examples to More on Algebra,
Section 29.  That later chapter is intentionally not imported here: this chapter records the
comparison warning, while its canonical complex and homology API belong to the deferred chapter.
-/

/-! ## The join counterexample -/

inductive joinExampleVariable
  | x
  | y
  | w
  | z (n : ℕ)
deriving DecidableEq

def joinExampleX (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .x

def joinExampleY (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .y

def joinExampleW (k : Type u) [CommRing k] :
    MvPolynomial joinExampleVariable k := MvPolynomial.X .w

def joinExampleZ (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial joinExampleVariable k := MvPolynomial.X (.z n)

def joinExampleRelations (k : Type u) [CommRing k] :
    Set (MvPolynomial joinExampleVariable k) :=
  {joinExampleY k ^ 2 * joinExampleZ k 0 - joinExampleW k * joinExampleX k} ∪
    Set.range (fun n : ℕ => joinExampleZ k n - joinExampleY k * joinExampleZ k (n + 1))

def joinExampleIdeal (k : Type u) [CommRing k] :
    Ideal (MvPolynomial joinExampleVariable k) := Ideal.span (joinExampleRelations k)

abbrev joinExampleRing (k : Type u) [Field k] :=
  MvPolynomial joinExampleVariable k ⧸ joinExampleIdeal k

def joinExampleXbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleX k)

def joinExampleYbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleY k)

def joinExampleWbar (k : Type u) [Field k] : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleW k)

def joinExampleZbar (k : Type u) [Field k] (n : ℕ) : joinExampleRing k :=
  Ideal.Quotient.mk (joinExampleIdeal k) (joinExampleZ k n)

theorem join_example_defining_relation (k : Type u) [Field k] :
    joinExampleYbar k ^ 2 * joinExampleZbar k 0 =
      joinExampleWbar k * joinExampleXbar k := by
  sorry

theorem join_example_z_relation (k : Type u) [Field k] (n : ℕ) :
    joinExampleZbar k n = joinExampleYbar k * joinExampleZbar k (n + 1) := by
  sorry

theorem join_example_x_is_non_zero_divisor (k : Type u) [Field k] :
    IsSMulRegular (joinExampleRing k) (joinExampleXbar k) := by
  sorry

theorem join_example_ybar_is_quasiRegular (k : Type u) [Field k] :
    IsQuasiRegular (joinExampleRing k ⧸ Ideal.span {joinExampleXbar k})
      [Ideal.Quotient.mk (Ideal.span {joinExampleXbar k}) (joinExampleYbar k)] := by
  sorry

theorem join_example_pair_is_not_quasiRegular (k : Type u) [Field k] :
    ¬ IsQuasiRegular (joinExampleRing k) [joinExampleXbar k, joinExampleYbar k] := by
  sorry

theorem join_example_wbar_mul_xbar_mod_xy_zero (k : Type u) [Field k] :
    Ideal.Quotient.mk (Ideal.span {joinExampleXbar k, joinExampleYbar k})
        (joinExampleWbar k * joinExampleXbar k) = 0 := by
  sorry

theorem join_example_wbar_mod_xy_is_nonzero (k : Type u) [Field k] :
    Ideal.Quotient.mk (Ideal.span {joinExampleXbar k, joinExampleYbar k})
        (joinExampleWbar k) ≠ 0 := by
  sorry

/-! ## Quotienting by the separated part -/

abbrev quasiRegularSeparatedRing
    {R : Type u} [CommRing R] (I : Ideal R) :=
  R ⧸ Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I

abbrev quasiRegularSeparatedModule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :=
  M ⧸ Formalization.Books.Algebra.Unit51.powersIntersectionSubmodule (M := M) I

theorem quasiRegularSeparatedModule_is_torsion
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Module.IsTorsionBySet R (quasiRegularSeparatedModule (M := M) I)
      (Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I) := by
  sorry

@[instance_reducible]
noncomputable def quasiRegularSeparatedModuleModule
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Module (quasiRegularSeparatedRing I) (quasiRegularSeparatedModule (M := M) I) :=
  (quasiRegularSeparatedModule_is_torsion I).module

theorem isMQuasiRegular_iff_separated
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    let I := Ideal.ofList f
    letI := quasiRegularSeparatedModuleModule (M := M) I
    IsMQuasiRegular R M f ↔
      IsMQuasiRegular (quasiRegularSeparatedRing I)
        (quasiRegularSeparatedModule (M := M) I)
        (f.map (Ideal.Quotient.mk
          (Formalization.Books.Algebra.Unit51.powersIntersectionIdeal I))) := by
  sorry

end

end Formalization.Books.Algebra.Unit69
