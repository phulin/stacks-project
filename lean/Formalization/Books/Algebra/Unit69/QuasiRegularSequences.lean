import Formalization.Books.Algebra.Unit51.MoreNoetherianRings
import Formalization.Books.Algebra.Unit68.RegularSequences
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial

/-!
# Commutative Algebra, Chapter 69: Quasi-regular sequences

The associated graded pieces below are written as nested submodule quotients.  This is the
canonical Mathlib presentation of `I ^ n M / I ^ (n + 1) M`: the denominator is
`I • ⊤` in the module `I ^ n • ⊤`, so that the quotient automatically has its natural
`R ⧸ I`-module structure.
-/

namespace Formalization.Books.Algebra.Unit69

open scoped DirectSum TensorProduct

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

/-- The elementary ideal-membership fact used to define the canonical monomial map. -/
theorem quasiRegularMonomialCoefficient_mem
    {R : Type u} [CommRing R] (f : List R) (d : Fin f.length →₀ ℕ) :
    quasiRegularMonomialCoefficient f d ∈
      (Ideal.ofList f) ^ quasiRegularDegree d := by
  classical
  let I := Ideal.ofList f
  have hgen : ∀ i : Fin f.length, f.get i ∈ I := by
    intro i
    exact Ideal.subset_span (by simp)
  have hprod : ∀ s : Finset (Fin f.length),
      s.prod (fun i => f.get i ^ d i) ∈ I ^ s.sum (fun i => d i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hh := Ideal.mul_mem_mul (Ideal.pow_mem_pow (hgen a) (d a)) ih
      simpa [Ideal.IsTwoSided.pow_add] using hh
  simpa [quasiRegularMonomialCoefficient, quasiRegularDegree, Finsupp.prod,
    Finsupp.sum, I] using (hprod d.support)

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

/-- Multiplication by an element of `I` kills the raw monomial map in the graded quotient. -/
theorem quasiRegularMonomialMapRaw_ker
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) :
    Ideal.ofList f • (⊤ : Submodule R M) ≤
      LinearMap.ker (quasiRegularMonomialMapRaw R M f d) := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m hm
    change quasiRegularMonomialMapRaw R M f d (r • m) = 0
    simp only [quasiRegularMonomialMapRaw, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero, map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    change quasiRegularMonomialMapRaw R M f d (x + y) = 0
    rw [(quasiRegularMonomialMapRaw R M f d).map_add, hx, hy, add_zero]

/-- The raw map is semilinear for the quotient map on scalars. -/
theorem quasiRegularMonomialMapRaw_map_smul_quotient
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (d : Fin f.length →₀ ℕ) (r : R) (m : M) :
    quasiRegularMonomialMapRaw R M f d (r • m) =
      Ideal.Quotient.mk (Ideal.ofList f) r •
        quasiRegularMonomialMapRaw R M f d m := by
  simp [quasiRegularMonomialMapRaw]

/- The quotient of a semilinear map by `I` is linear over `R ⧸ I`.  The statement is
   isolated because Mathlib exposes the quotient map naturally as a semilinear map. -/
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
  let := hN.module
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  exact g.map_smulₛₗ r x

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
  apply LinearMap.ext
  intro p
  dsimp [quasiRegularPolynomialMap]
  simp_rw [map_add, LinearMap.toSpanSingleton_add]
  exact Finsupp.sum_add

theorem quasiRegularPolynomialMap_smul
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (c : R ⧸ Ideal.ofList f)
    (m : M ⧸ (Ideal.ofList f • (⊤ : Submodule R M))) :
    quasiRegularPolynomialMap R M f (c • m) =
      c • quasiRegularPolynomialMap R M f m := by
  apply LinearMap.ext
  intro p
  dsimp [quasiRegularPolynomialMap]
  simp_rw [map_smul, LinearMap.toSpanSingleton_smul]
  rw [Finsupp.smul_sum]
  rfl

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

/-- The canonical map sends a pure monomial to the corresponding graded component. -/
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
  simp [quasiRegularCanonicalMap, quasiRegularBilinearMap, quasiRegularPolynomialMap]

/-- The canonical graded map is always surjective. -/
theorem quasiRegularCanonicalMap_surjective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) :
    Function.Surjective (quasiRegularCanonicalMap R M f) := by
  classical
  let I := Ideal.ofList f
  let P : ℕ → Submodule R M := fun n => I ^ n • (⊤ : Submodule R M)
  let G : ∀ n, Set (↥(P n)) := fun n =>
    {x | ∃ d : Fin f.length →₀ ℕ, ∃ hd : quasiRegularDegree d = n,
        ∃ m : M, x = ⟨quasiRegularMonomialCoefficient f d • m,
          Submodule.smul_mem_smul (by
            simpa [I, hd] using (quasiRegularMonomialCoefficient_mem f d))
            Submodule.mem_top⟩}
  let S : ∀ n, Submodule R (↥(P n)) := fun n => Submodule.span R (G n)
  have hcoeff (d : Fin f.length →₀ ℕ) (i : Fin f.length) :
      quasiRegularMonomialCoefficient f (d + Finsupp.single i 1) =
        quasiRegularMonomialCoefficient f d * f.get i := by
    change (d + Finsupp.single i 1).prod (fun j e => f.get j ^ e) =
      d.prod (fun j e => f.get j ^ e) * f.get i
    rw [Finsupp.prod_add_index' (h_zero := fun j => by exact pow_zero _)
      (h_add := fun j a b => by rw [pow_add])]
    rw [Finsupp.prod_single_index (by exact pow_zero _)]
    rw [pow_one]
  have hdeg (d : Fin f.length →₀ ℕ) (i : Fin f.length) :
      quasiRegularDegree (d + Finsupp.single i 1) =
        quasiRegularDegree d + 1 := by
    simp [quasiRegularDegree, Finsupp.sum_add_index]
  have hI (i : Fin f.length) : f.get i ∈ I := by
    simpa [I] using (Ideal.subset_span (show f.get i ∈ {r | r ∈ f} by simp))
  have hP (n : ℕ) (i : Fin f.length) (z : M) (hz : z ∈ P n) :
      f.get i • z ∈ P (n + 1) := by
    simpa [P, pow_succ', Submodule.mul_smul, mul_comm] using
      (Submodule.smul_mem_smul (hI i) hz)
  have hshift :
      ∀ (n : ℕ) (i : Fin f.length) (y : ↥(P n)), y ∈ S n →
        (⟨f.get i • (y : M), hP n i (y : M) y.property⟩ : ↥(P (n + 1))) ∈
          S (n + 1) := by
    intro n i y hy
    change y ∈ Submodule.span R (G n) at hy
    refine Submodule.span_induction (p := fun (z : ↥(P n)) hz =>
        (⟨f.get i • (z : M), hP n i (z : M) z.property⟩ : ↥(P (n + 1))) ∈
          S (n + 1)) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨d, hd, m, rfl⟩
      apply Submodule.subset_span
      refine ⟨d + Finsupp.single i 1, ?_, m, ?_⟩
      · rw [hdeg, hd]
      · apply Subtype.ext
        simp only [Subtype.coe_mk]
        simp [hcoeff, smul_smul, smul_eq_mul, mul_comm]
    · convert Submodule.zero_mem (S (n + 1)) using 1
      apply Subtype.ext
      simp
    · intro y z hy hz Cy Cz
      simpa [add_smul] using (Submodule.add_mem (S (n + 1)) Cy Cz)
    · intro a z hz Cz
      convert Submodule.smul_mem (S (n + 1)) a Cz using 1
      apply Subtype.ext
      simp [smul_smul, mul_comm]
  have hmul (n : ℕ) (b : R) (hb : b ∈ I) (r : R) (hr : r ∈ I ^ n) :
      b * r ∈ I ^ (n + 1) := by
    simpa [I, Ideal.ofList, pow_succ', smul_eq_mul, mul_comm] using
      (Submodule.smul_mem_smul hb hr)
  have hpow :
      ∀ (n : ℕ) (r : R) (hr : r ∈ I ^ n) (m : M),
        (⟨r • m, Submodule.smul_mem_smul hr Submodule.mem_top⟩ : ↥(P n)) ∈ S n := by
    intro n r hr
    refine Submodule.pow_induction_on_left' I
      (C := fun n r hr => ∀ m : M,
        (⟨r • m, Submodule.smul_mem_smul hr Submodule.mem_top⟩ : ↥(P n)) ∈ S n) ?_ ?_ ?_ hr
    · intro a m
      apply Submodule.subset_span
      refine ⟨0, ?_, a • m, ?_⟩
      · simp [quasiRegularDegree]
      · apply Subtype.ext
        simp [quasiRegularMonomialCoefficient]
    · intro x y i hx hy Cx Cy m
      simpa [add_smul] using (Submodule.add_mem (S i) (Cx m) (Cy m))
    · intro a ha i r hr Cr
      have ha' : a ∈ Submodule.span R {r | r ∈ f} := by
        simpa [I, Ideal.ofList] using ha
      refine Submodule.span_induction (p := fun b hb => ∀ m : M,
          (⟨(b * r) • m,
            Submodule.smul_mem_smul (hmul i b (by simpa [I] using hb) r hr)
              Submodule.mem_top⟩ : ↥(P (i + 1))) ∈ S (i + 1)) ?_ ?_ ?_ ?_ ha'
      · intro b hb m
        obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
        subst b
        have hs := hshift i j
          (⟨r • m, Submodule.smul_mem_smul hr Submodule.mem_top⟩ : ↥(P i))
          (Cr m)
        simpa [P, pow_succ', Submodule.mul_smul, smul_smul, mul_comm, mul_left_comm,
          mul_assoc, smul_eq_mul] using hs
      · intro m
        convert Submodule.zero_mem (S (i + 1)) using 1
        apply Subtype.ext
        simp
      · intro b c hb hc Hb Hc m
        simpa [add_mul, add_smul] using (Submodule.add_mem (S (i + 1)) (Hb m) (Hc m))
      · intro a b hb Hb m
        simpa [mul_smul, smul_eq_mul, mul_assoc] using
          (Submodule.smul_mem (S (i + 1)) a (Hb m))
  have hspan : ∀ (n : ℕ) (x : ↥(P n)), x ∈ S n := by
    intro n x
    change (⟨(x : M), x.property⟩ : ↥(P n)) ∈ S n
    refine Submodule.smul_induction_on' (p := fun z hz =>
        (⟨z, hz⟩ : ↥(P n)) ∈ S n) x.property ?_ ?_
    · intro r hr m hm
      exact hpow n r hr m
    · intro y hy z hz Cy Cz
      simpa using (Submodule.add_mem (S n) Cy Cz)
  have hmono :
      ∀ (d : Fin f.length →₀ ℕ) (m : M),
        quasiRegularMonomialMapQuotient R M f d (Submodule.Quotient.mk m) =
          Submodule.Quotient.mk
            ⟨quasiRegularMonomialCoefficient f d • m,
              Submodule.smul_mem_smul (quasiRegularMonomialCoefficient_mem f d)
                Submodule.mem_top⟩ := by
    intro d m
    simp [quasiRegularMonomialMapQuotient, quotientSemilinearMapToLinear,
      quasiRegularMonomialMapRaw]
    rfl
  have hgood :
      ∀ (n : ℕ) (y : ↥(P n)), y ∈ S n →
        ∃ z : quasiRegularSource R M f,
          quasiRegularCanonicalMap R M f z =
            (DirectSum.lof (R ⧸ I) ℕ (fun n => quasiRegularPiece R M I n) n)
              (Submodule.Quotient.mk y) := by
    intro n y hy
    change y ∈ Submodule.span R (G n) at hy
    refine Submodule.span_induction (p := fun z _ =>
        ∃ w : quasiRegularSource R M f,
          quasiRegularCanonicalMap R M f w =
            (DirectSum.lof (R ⧸ I) ℕ (fun n => quasiRegularPiece R M I n) n)
              (Submodule.Quotient.mk z)) ?_ ?_ ?_ ?_ hy
    · intro z hz
      rcases hz with ⟨d, hd, m, rfl⟩
      subst n
      refine ⟨Submodule.Quotient.mk m ⊗ₜ[R ⧸ I] MvPolynomial.monomial d 1, ?_⟩
      rw [quasiRegularCanonicalMap_monomial]
      simpa [I] using congrArg
        (DirectSum.lof (R ⧸ I) ℕ (fun n => quasiRegularPiece R M I n)
          (quasiRegularDegree d)) (hmono d m)
    · exact ⟨0, by simp⟩
    · intro y z hy hz ⟨uy, huy⟩ ⟨uz, huz⟩
      refine ⟨uy + uz, ?_⟩
      rw [map_add, huy, huz]
      simp
    · intro a z hz ⟨uz, huz⟩
      refine ⟨(Ideal.Quotient.mk I a) • uz, ?_⟩
      rw [map_smul, huz]
      rw [← (DirectSum.lof (R ⧸ I) ℕ
        (fun n => quasiRegularPiece R M I n) n).map_smul]
      have hN := Module.isTorsionBySet_quotient_ideal_smul
        (M := ↥(I ^ n • (⊤ : Submodule R M))) (I := I)
      rw [Module.IsTorsionBySet.mk_smul hN]
      rw [Submodule.Quotient.mk_smul]
  intro x
  refine DirectSum.induction_on x ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro n y
    unfold quasiRegularPiece at y
    refine Submodule.Quotient.induction_on
      (p := Ideal.ofList f •
        (⊤ : Submodule R ↥((Ideal.ofList f) ^ n • (⊤ : Submodule R M)))) y ?_
    intro z
    rcases hgood n z (by simpa [P, I] using hspan n z) with ⟨w, hw⟩
    simpa [I] using ⟨w, hw⟩
  · intro x y hx hy
    rcases hx with ⟨ux, hux⟩
    rcases hy with ⟨uy, huy⟩
    exact ⟨ux + uy, by rw [map_add, hux, huy]⟩

/-! ## Definition and basic properties -/

/-- A sequence is `M`-quasi-regular when the canonical graded map is bijective. -/
def IsMQuasiRegular
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) : Prop :=
  Function.Bijective (quasiRegularCanonicalMap R M f)

/-- A sequence is quasi-regular when it is `R`-quasi-regular on the regular module. -/
def IsQuasiRegular
    (R : Type u) [CommRing R] (f : List R) : Prop :=
  IsMQuasiRegular R R f

/- A bijective canonical map is the actual module-level isomorphism used by the
   source's associated-graded identification. -/
noncomputable def quasiRegularCanonicalEquiv
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (f : List R) (hf : IsMQuasiRegular R M f) :
    quasiRegularSource R M f ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R M (Ideal.ofList f) :=
  LinearEquiv.ofBijective (quasiRegularCanonicalMap R M f) hf

theorem isMQuasiRegular_iff_of_perm
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : List R} (hfg : f.Perm g) :
    IsMQuasiRegular R M f ↔ IsMQuasiRegular R M g := by
  sorry

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
with the associated graded object, as in the textbook. -/
noncomputable def quasiRegular_graded_ring_identification
    {R : Type u} [CommRing R] (f : List R)
    (hf : IsQuasiRegular R f) :
    MvPolynomial (Fin f.length) (R ⧸ Ideal.ofList f) ≃ₗ[R ⧸ Ideal.ofList f]
      quasiRegularTarget R R (Ideal.ofList f) :=
by
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
  sorry

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

/-
PRIOR ATTEMPT: The source remark refers to the Koszul complex and explicitly defers its
definitions and examples to More on Algebra, Section 29.  The declarations below used an
arbitrary family of homology types; they were not tied to the canonical Koszul complex of the
sequence, so they did not provide valid interfaces for the source assertions.  The block is
retained for review history and is intentionally not part of this chapter's API.

/-! ## Koszul and `H₁` regularity -/

/-
Mathlib has no Koszul-complex or Koszul-homology API (the regular-sequence file records this as
an explicit TODO).  The following data type is therefore the chapter-facing interface for the
canonical complex `K₍•₎(R, f)`: a later chapter can supply its actual homology objects without
changing these predicates.  Unlike an existential placeholder, the regularity predicates below
take that homology data explicitly and say exactly that positive-degree, respectively first,
homology is zero.  They are intentionally not used to replace the canonical quasi-regular
definition above.
-/

structure KoszulComplexData (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] (f : List R) : Type (max u v + 2) where
  /-- The homology objects of the Koszul complex. -/
  homology : ℕ → Type v

def IsKoszulRegular
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (K : KoszulComplexData R M f) : Prop :=
  ∀ i, 0 < i → Subsingleton (K.homology i)

def IsHOneRegular
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (K : KoszulComplexData R M f) : Prop :=
  Subsingleton (K.homology 1)

theorem regular_koszul_hone_quasi_implications
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f : List R} (K : KoszulComplexData R M f) :
    RingTheory.Sequence.IsRegular M f →
      IsKoszulRegular K ∧
        (IsKoszulRegular K → IsHOneRegular K) ∧
          (IsHOneRegular K → IsMQuasiRegular R M f) := by
  sorry

/-- The source's warning that none of the three comparison arrows has a converse in general.
The universal negations are restricted to local, non-Noetherian rings whose sequence generates
the maximal ideal, exactly the setting mentioned in the remark. -/
theorem koszul_regularities_not_reversible :
    (¬ ∀ (R : Type u) [CommRing R] [IsLocalRing R]
        (hnoeth : ¬ IsNoetherianRing R) (f : List R)
        (hmax : Ideal.ofList f = IsLocalRing.maximalIdeal R)
        (K : KoszulComplexData R R f),
        IsKoszulRegular K → RingTheory.Sequence.IsRegular R f) ∧
      (¬ ∀ (R : Type u) [CommRing R] [IsLocalRing R]
        (hnoeth : ¬ IsNoetherianRing R) (f : List R)
        (hmax : Ideal.ofList f = IsLocalRing.maximalIdeal R)
        (K : KoszulComplexData R R f),
        IsHOneRegular K → IsKoszulRegular K) ∧
      (¬ ∀ (R : Type u) [CommRing R] [IsLocalRing R]
        (hnoeth : ¬ IsNoetherianRing R) (f : List R)
        (hmax : Ideal.ofList f = IsLocalRing.maximalIdeal R)
        (K : KoszulComplexData R R f),
        IsQuasiRegular R f → IsHOneRegular K) := by
  sorry
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
  {MvPolynomial.C 1 * joinExampleY k ^ 2 * joinExampleZ k 0 -
      joinExampleW k * joinExampleX k} ∪
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
    joinExampleZbar k n =
      joinExampleYbar k * joinExampleZbar k (n + 1) := by
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
