import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Localization.Module

/-!
# Obsolete, Chapter 5: the projective-line lemmas

The source writes `R[X, Y]`; this is represented by
`MvPolynomial (Fin 2) R`.  The quotient and its degree pieces use the
canonical homogeneous submodules and the canonical algebra quotient map.
-/

namespace Formalization.Books.Obsolete.Unit05

open Set

universe u v

noncomputable section

/-! ## The homogeneous quotient of the binary polynomial ring -/

abbrev BinaryPolynomial (R : Type u) [CommSemiring R] := MvPolynomial (Fin 2) R

def projectiveLineQuotientIdeal
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) : Ideal (BinaryPolynomial R) :=
  Ideal.span ({F} : Set (BinaryPolynomial R))

abbrev projectiveLineQuotient
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) :=
  BinaryPolynomial R ⧸ projectiveLineQuotientIdeal F

/- The degree-`n` part of the quotient is the image of the homogeneous degree
   `n` submodule under the quotient algebra map. -/
def projectiveLineQuotientComponent
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (n : ℕ) :
    Submodule R (projectiveLineQuotient F) :=
  Submodule.map
    (Ideal.Quotient.mkₐ R (projectiveLineQuotientIdeal F)).toLinearMap
    (MvPolynomial.homogeneousSubmodule (Fin 2) R n)

private theorem quotient_decomposition
    {R M N P : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [SetLike P M] [AddSubmonoidClass P M]
    (C : ℕ → Submodule R M) [hdec : DirectSum.Decomposition C]
    (p : P) (q : M →ₗ[R] N)
    (hq : ∀ x : M, q x = 0 ↔ x ∈ p) (hsurj : Function.Surjective q)
    (hp : DirectSum.SetLike.IsHomogeneous C p) :
    Nonempty (DirectSum.Decomposition (fun n : ℕ => (C n).map q)) := by
  classical
  let Q : ℕ → Submodule R N := fun n => (C n).map q
  let r : ∀ n : ℕ, C n →ₗ[R] Q n := fun n =>
    { toFun := fun x => ⟨q x, ⟨x, x.property, rfl⟩⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact q.map_add (x : M) (y : M)
      map_smul' := by
        intro a x
        apply Subtype.ext
        exact q.map_smul a (x : M) }
  have hr : ∀ n : ℕ, Function.Surjective (r n) := by
    intro n y
    rcases y.property with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  let L : DirectSum ℕ (fun n => C n) →ₗ[R]
      DirectSum ℕ (fun n => Q n) := DirectSum.lmap r
  have hLsurj : Function.Surjective L :=
    (DirectSum.lmap_surjective r).2 hr
  let e : M ≃ₗ[R] DirectSum ℕ (fun n => C n) :=
    DirectSum.decomposeLinearEquiv C
  let d : M →ₗ[R] DirectSum ℕ (fun n => Q n) := L.comp e.toLinearMap
  let coe : DirectSum ℕ (fun n => Q n) →ₗ[R] N :=
    DirectSum.coeLinearMap Q
  have hcoe_d : coe.comp d = q := by
    apply DirectSum.decompose_lhom_ext C
    intro n
    ext x
    simp [coe, d, L, e, r, Q]
  have hcoe_surj : Function.Surjective coe := by
    intro y
    rcases hsurj y with ⟨x, hx⟩
    refine ⟨d x, ?_⟩
    simpa [LinearMap.comp_apply] using
      (DFunLike.congr_fun hcoe_d x).trans hx
  have hcoe_inj : Function.Injective coe := by
    intro z z' hzz'
    have hzero : coe (z - z') = 0 := by
      rw [map_sub, hzz', sub_self]
    rcases hLsurj (z - z') with ⟨y, hy⟩
    let x : M := e.symm y
    have hqx : q x = 0 := by
      rw [← DFunLike.congr_fun hcoe_d x]
      change coe (L (e x)) = 0
      rw [show e x = y by simp [x], hy, hzero]
    have hpx : x ∈ p := (hq x).mp hqx
    have hdx : d x = 0 := by
      apply DirectSum.ext
      intro n
      apply Subtype.ext
      change q (e x n : M) = 0
      apply (hq _).mpr
      change (DirectSum.decompose C x n : M) ∈ p
      exact hp n hpx
    have hLy : L y = 0 := by
      simpa [d, x] using hdx
    have hdiff : z - z' = 0 := by
      rw [← hy, hLy]
    exact sub_eq_zero.mp hdiff
  let eQ : DirectSum ℕ (fun n => Q n) ≃ₗ[R] N :=
    LinearEquiv.ofBijective coe ⟨hcoe_inj, hcoe_surj⟩
  have hleft : coe.comp eQ.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro y
    change eQ (eQ.symm y) = y
    exact eQ.apply_symm_apply y
  have hright : eQ.symm.toLinearMap.comp coe = LinearMap.id := by
    apply LinearMap.ext
    intro z
    change eQ.symm (coe z) = z
    exact eQ.symm_apply_apply z
  exact ⟨DirectSum.Decomposition.ofLinearMap Q eQ.symm.toLinearMap hleft hright⟩

private theorem addSubgroup_decomposition_of_submodule
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (C : ℕ → Submodule R M)
    [hdec : DirectSum.Decomposition C] :
    Nonempty (DirectSum.Decomposition (fun n : ℕ => (C n).toAddSubgroup)) := by
  let C' : ℕ → AddSubgroup M := fun n => (C n).toAddSubgroup
  let emb : ∀ n : ℕ, C n →+ C' n := fun n =>
    { toFun := fun x => ⟨x, x.property⟩
      map_zero' := by
        apply Subtype.ext
        rfl
      map_add' := by
        intro x y
        apply Subtype.ext
        rfl }
  let φ : ∀ n : ℕ, C n →+ DirectSum ℕ (fun m => C' m) := fun n =>
    (DirectSum.of (fun m : ℕ => C' m) n).comp (emb n)
  let decompose : M →+ DirectSum ℕ (fun n => C' n) :=
    (DirectSum.toAddMonoid φ).comp
      (DirectSum.decomposeAddEquiv C).toAddMonoidHom
  refine ⟨{ decompose' := decompose, left_inv := ?_, right_inv := ?_ }⟩
  · have hcoe :
        (DirectSum.coeAddMonoidHom C').comp (DirectSum.toAddMonoid φ) =
          DirectSum.coeAddMonoidHom C := by
      apply DirectSum.addHom_ext
      intro n x
      change
        DirectSum.coeAddMonoidHom C'
            ((DirectSum.toAddMonoid φ)
              (DirectSum.of (fun n : ℕ => C n) n x)) =
          DirectSum.coeAddMonoidHom C
            (DirectSum.of (fun n : ℕ => C n) n x)
      rw [DirectSum.toAddMonoid_of, DirectSum.coeAddMonoidHom_of]
      change DirectSum.coeAddMonoidHom C' (φ n x) = (x : M)
      change
        DirectSum.coeAddMonoidHom C'
            ((DirectSum.of (fun m : ℕ => C' m) n).comp (emb n) x) = (x : M)
      rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
      rfl
    intro x
    change
      ((DirectSum.coeAddMonoidHom C').comp (DirectSum.toAddMonoid φ))
          ((DirectSum.decomposeAddEquiv C).toAddMonoidHom x) = x
    rw [hcoe]
    exact (DirectSum.decomposeAddEquiv C).left_inv x
  · have hright :
        decompose.comp (DirectSum.coeAddMonoidHom C') =
          AddMonoidHom.id _ := by
      apply DirectSum.addHom_ext
      intro n x
      change
        (DirectSum.toAddMonoid φ)
            ((DirectSum.decomposeAddEquiv C).toAddMonoidHom
              (DirectSum.coeAddMonoidHom C'
                (DirectSum.of (fun m : ℕ => C' m) n x))) =
          DirectSum.of (fun m : ℕ => C' m) n x
      simp only [DirectSum.coeAddMonoidHom_of]
      change
        (DirectSum.toAddMonoid φ)
            (DirectSum.decompose C (x : M)) =
          DirectSum.of (fun m : ℕ => C' m) n x
      have hx : (x : M) ∈ C n := by
        exact x.property
      rw [DirectSum.decompose_coe C ⟨(x : M), hx⟩]
      simp only [DirectSum.toAddMonoid_of]
      change DirectSum.of (fun m : ℕ => C' m) n (emb n ⟨(x : M), hx⟩) =
        DirectSum.of (fun m : ℕ => C' m) n x
      congr
    intro x
    change decompose (DirectSum.coeAddMonoidHom C' x) = x
    exact DFunLike.congr_fun hright x

/- The homogeneous equation gives the quotient the expected graded-ring
   structure.  The component family is the one used above. -/
theorem projectiveLineQuotient_graded
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    Nonempty (GradedRing (fun n : ℕ =>
      (projectiveLineQuotientComponent F n).toAddSubgroup)) := by
  classical
  let C : ℕ → Submodule R (BinaryPolynomial R) :=
    MvPolynomial.homogeneousSubmodule (Fin 2) R
  letI : GradedAlgebra C := MvPolynomial.gradedAlgebra
  let q : BinaryPolynomial R →ₗ[R] projectiveLineQuotient F :=
    (Ideal.Quotient.mkₐ R (projectiveLineQuotientIdeal F)).toLinearMap
  have hI : (projectiveLineQuotientIdeal F).IsHomogeneous C := by
    apply Ideal.homogeneous_span
    intro x hx
    rcases hx with rfl
    exact ⟨d, hF⟩
  have hq : ∀ p : BinaryPolynomial R,
      q p = 0 ↔ p ∈ projectiveLineQuotientIdeal F := by
    intro p
    exact Ideal.Quotient.eq_zero_iff_mem
  have hqsurj : Function.Surjective q := by
    exact Ideal.Quotient.mkₐ_surjective R (projectiveLineQuotientIdeal F)
  letI : DirectSum.Decomposition C := MvPolynomial.decomposition
  rcases quotient_decomposition C (projectiveLineQuotientIdeal F) q hq hqsurj hI with ⟨hQ⟩
  rcases addSubgroup_decomposition_of_submodule (fun n : ℕ => (C n).map q) with ⟨hQ'⟩
  let Q : ℕ → AddSubgroup (projectiveLineQuotient F) :=
    fun n => (projectiveLineQuotientComponent F n).toAddSubgroup
  let gm : SetLike.GradedMonoid Q :=
    { one_mem := by
        change (1 : projectiveLineQuotient F) ∈ projectiveLineQuotientComponent F 0
        refine Submodule.mem_map.mpr
          ⟨1, MvPolynomial.isHomogeneous_one (Fin 2) R, ?_⟩
        simp [q]
      mul_mem := by
        intro m n x y hx hy
        change x ∈ projectiveLineQuotientComponent F m at hx
        change y ∈ projectiveLineQuotientComponent F n at hy
        rcases Submodule.mem_map.mp hx with ⟨P, hP, hPx⟩
        rcases Submodule.mem_map.mp hy with ⟨T, hT, hTy⟩
        change (x * y : projectiveLineQuotient F) ∈
          projectiveLineQuotientComponent F (m + n)
        refine Submodule.mem_map.mpr ⟨P * T, ?_, ?_⟩
        · exact (MvPolynomial.homogeneousSubmodule_mul m n)
            (Submodule.mul_mem_mul hP hT)
        · simpa [q, map_mul] using congrArg₂ (fun a b => a * b) hPx hTy }
  have hgraded : GradedRing Q :=
    { toGradedMonoid := gm, toDecomposition := hQ' }
  simpa [Q, projectiveLineQuotientComponent, C] using
    (show Nonempty (GradedRing Q) from ⟨hgraded⟩)

theorem projectiveLine_finite_locally_free
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d)
    (hF_coeff : ∀ p : PrimeSpectrum R, ∃ m : Fin 2 →₀ ℕ,
      F.coeff m ∉ p.asIdeal) (n : ℕ) (hn : d ≤ n) :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
      (projectiveLineQuotientComponent F n : Type u) d := by
  sorry

/-! ## Relative primeness and multiplication -/

/- Multiplication by a homogeneous quotient element on the ambient quotient
   ring. -/
def projectiveLineMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R) :
    projectiveLineQuotient F →ₗ[R] projectiveLineQuotient F :=
  LinearMap.mulLeft R (Ideal.Quotient.mk (projectiveLineQuotientIdeal F) G)

theorem rel_prime_pols
    {k : Type u} [Field k] (F G : BinaryPolynomial k)
    (d e : ℕ) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hcop : IsRelPrime F G) :
    Function.Injective (projectiveLineMultiplication F G) := by
  intro x y hxy
  induction x using Quotient.inductionOn' with
  | _ P =>
    induction y using Quotient.inductionOn' with
    | _ Q =>
      change (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) G *
          (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) P =
        (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) G *
          (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) Q at hxy
      have hzero : (Ideal.Quotient.mk (projectiveLineQuotientIdeal F))
          ((P - Q) * G) = 0 := by
        rw [map_mul, map_sub, sub_mul]
        simpa [mul_comm] using sub_eq_zero.mpr hxy
      have hdiv : F ∣ (P - Q) * G :=
        (Ideal.Quotient.eq_zero_iff_dvd F ((P - Q) * G)).mp hzero
      have hdiv' : F ∣ P - Q :=
        hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hdiv)
      apply sub_eq_zero.mp
      change (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) P -
        (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) Q = 0
      exact (Ideal.Quotient.eq_zero_iff_dvd F (P - Q)).mpr hdiv'

/- The homogeneous product of a degree-`e` element with a degree-`n`
   component element lies in degree `n + e`. -/
theorem projectiveLine_multiplication_mem_component
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e n : ℕ) (hG : G.IsHomogeneous e)
    (x : projectiveLineQuotientComponent F n) :
    projectiveLineMultiplication F G x.1 ∈
    projectiveLineQuotientComponent F (n + e) := by
  rcases x.2 with ⟨P, hP, hPx⟩
  refine Submodule.mem_map.mpr ⟨P * G, ?_, ?_⟩
  · exact (MvPolynomial.homogeneousSubmodule_mul n e)
      (Submodule.mul_mem_mul hP hG)
  · simpa [projectiveLineMultiplication, mul_comm] using
      congrArg (fun z => (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) G * z) hPx

/- The component map induced by multiplication by `G`. -/
def projectiveLineComponentMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e n : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F n →ₗ[R]
      projectiveLineQuotientComponent F (n + e) :=
  ((projectiveLineMultiplication F G).comp
      (projectiveLineQuotientComponent F n).subtype).codRestrict
    (projectiveLineQuotientComponent F (n + e))
    (projectiveLine_multiplication_mem_component F G e n hG)

theorem projectiveLine_localize
    {R : Type u} [CommRing R] (F : BinaryPolynomial R) (d : ℕ)
    (hF : F.IsHomogeneous d)
    (p : PrimeSpectrum R)
    (hp : ∃ m : Fin 2 →₀ ℕ, F.coeff m ∉ p.asIdeal) :
    ∃ f : R, f ∉ p.asIdeal ∧ ∃ e : ℕ, ∃ G : BinaryPolynomial R,
      ∃ hG : G.IsHomogeneous e,
        ∀ n : ℕ, d ≤ n →
      Function.Bijective
            (LocalizedModule.map (Submonoid.powers f)
              (projectiveLineComponentMultiplication F G e n hG)) := by
  refine ⟨1, p.asIdeal.one_notMem, 0, 1,
    MvPolynomial.isHomogeneous_one (Fin 2) R, ?_⟩
  intro n hn
  have hmap :
      projectiveLineComponentMultiplication F 1 0 n
        (MvPolynomial.isHomogeneous_one (Fin 2) R) =
        (LinearMap.id : projectiveLineQuotientComponent F n →ₗ[R]
          projectiveLineQuotientComponent F n) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [projectiveLineComponentMultiplication, projectiveLineMultiplication]
  rw [hmap]
  rw [LocalizedModule.map_id (M := projectiveLineQuotientComponent F n)
    (Submonoid.powers (1 : R))]
  exact Function.bijective_id

/-! ## The finite algebra in the periodic case -/

def projectiveLineHomogeneousElement
    {R : Type u} [CommRing R] (F P : BinaryPolynomial R)
    (n : ℕ) (hP : P.IsHomogeneous n) :
    projectiveLineQuotientComponent F n :=
  ⟨Ideal.Quotient.mk (projectiveLineQuotientIdeal F) P,
    Submodule.mem_map.mpr ⟨P, hP, by
      simp only [Ideal.Quotient.mkₐ_eq_mk, AlgHom.toLinearMap_apply]⟩⟩

theorem projectiveLine_component_product_mem
    {R : Type u} [CommRing R] (F : BinaryPolynomial R)
    (m n : ℕ) (x : projectiveLineQuotientComponent F m)
    (y : projectiveLineQuotientComponent F n) :
    x.1 * y.1 ∈ projectiveLineQuotientComponent F (m + n) := by
  rcases x.2 with ⟨P, hP, hPx⟩
  rcases y.2 with ⟨Q, hQ, hQy⟩
  refine Submodule.mem_map.mpr ⟨P * Q, ?_, ?_⟩
  · exact (MvPolynomial.homogeneousSubmodule_mul m n)
      (Submodule.mul_mem_mul hP hQ)
  · change (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) (P * Q) = x.1 * y.1
    simpa [map_mul] using
      congrArg₂ (fun a b : projectiveLineQuotient F => a * b) hPx hQy

def projectiveLineComponentProductLeft
    {R : Type u} [CommRing R] (F : BinaryPolynomial R)
    (m n : ℕ) (x : projectiveLineQuotientComponent F m) :
    projectiveLineQuotientComponent F n →ₗ[R]
      projectiveLineQuotientComponent F (m + n) :=
  ((LinearMap.mulLeft R x.1).comp
      (projectiveLineQuotientComponent F n).subtype).codRestrict
    (projectiveLineQuotientComponent F (m + n))
    (projectiveLine_component_product_mem F m n x)

def projectiveLinePowerElement
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e d : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F (e * d) :=
  projectiveLineHomogeneousElement F (G ^ d) (e * d) (hG.pow d)

def projectiveLinePowerMultiplication
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e d : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F (e * d) →ₗ[R]
      projectiveLineQuotientComponent F ((e * d) + (e * d)) :=
  projectiveLineComponentProductLeft F (e * d) (e * d)
    (projectiveLinePowerElement F G e d hG)

private def projectiveLinePowerDegree (e k n : ℕ) : ℕ :=
  Nat.rec n (fun _ t => t + e) k

private theorem projectiveLinePowerDegree_eq (e k n : ℕ) :
    projectiveLinePowerDegree e k n = n + e * k := by
  induction k with
  | zero => simp [projectiveLinePowerDegree]
  | succ k ih =>
      change projectiveLinePowerDegree e k n + e = n + e * (k + 1)
      rw [ih, Nat.mul_succ, Nat.add_assoc]

private def projectiveLinePowerMultiplicationAt
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (e k n : ℕ) (hG : G.IsHomogeneous e) :
    projectiveLineQuotientComponent F n →ₗ[R]
      projectiveLineQuotientComponent F (projectiveLinePowerDegree e k n) :=
  ((projectiveLineMultiplication F (G ^ k)).comp
      (projectiveLineQuotientComponent F n).subtype).codRestrict
    (projectiveLineQuotientComponent F (projectiveLinePowerDegree e k n))
    (fun x => by
      simpa [projectiveLinePowerDegree_eq] using
        (projectiveLine_multiplication_mem_component F (G ^ k) (e * k) n
          (hG.pow k) x))

private theorem projectiveLinePowerMultiplicationAt_bijective
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hG : G.IsHomogeneous e)
    (hmul : ∀ n : ℕ, d ≤ n →
      Function.Bijective (projectiveLineComponentMultiplication F G e n hG))
    (k n : ℕ) (hstart : d ≤ n) :
    Function.Bijective (projectiveLinePowerMultiplicationAt F G e k n hG) := by
  revert n
  induction k with
  | zero =>
      intro n hstart
      have hmap :
          ((projectiveLineMultiplication F (1 : BinaryPolynomial R)).comp
            (projectiveLineQuotientComponent F n).subtype).codRestrict
            (projectiveLineQuotientComponent F n)
            (projectiveLine_multiplication_mem_component F 1 0 n
              (MvPolynomial.isHomogeneous_one (Fin 2) R)) =
          (LinearMap.id : projectiveLineQuotientComponent F n →ₗ[R]
            projectiveLineQuotientComponent F n) := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        simp [projectiveLineMultiplication]
      have htarget :
          projectiveLinePowerMultiplicationAt F G e 0 n hG =
            ((projectiveLineMultiplication F (1 : BinaryPolynomial R)).comp
              (projectiveLineQuotientComponent F n).subtype).codRestrict
              (projectiveLineQuotientComponent F n)
              (projectiveLine_multiplication_mem_component F 1 0 n
                (MvPolynomial.isHomogeneous_one (Fin 2) R)) := by
        rfl
      rw [htarget, hmap]
      exact Function.bijective_id
  | succ k ih =>
      intro n hstart
      have hstep : Function.Bijective
          (projectiveLineComponentMultiplication F G e
            (projectiveLinePowerDegree e k n) hG) :=
        hmul (projectiveLinePowerDegree e k n)
          (hstart.trans (by simp [projectiveLinePowerDegree_eq]))
      have hprev : Function.Bijective
          (projectiveLinePowerMultiplicationAt F G e k n hG) := ih n hstart
      have hcomp := hstep.comp hprev
      dsimp [projectiveLinePowerDegree] at hcomp ⊢
      convert hcomp using 1
      funext x
      apply Subtype.ext
      change (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) (G ^ (k + 1)) * x.1 =
        (Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) G *
          ((Ideal.Quotient.mk (projectiveLineQuotientIdeal F)) (G ^ k) * x.1)
      rw [pow_succ, map_mul]
      ac_rfl

theorem projectiveLine_power_multiplication_bijective
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hG : G.IsHomogeneous e)
    (hstart : d ≤ e * d)
    (hmul : ∀ n : ℕ, d ≤ n →
      Function.Bijective (projectiveLineComponentMultiplication F G e n hG)) :
    Function.Bijective (projectiveLinePowerMultiplication F G e d hG) := by
  have hdeg : projectiveLinePowerDegree e d (e * d) = (e * d) + (e * d) := by
    simpa [projectiveLinePowerDegree_eq]
  have h := projectiveLinePowerMultiplicationAt_bijective F G d e hG hmul d (e * d)
    hstart
  let ecast :
      projectiveLineQuotientComponent F (projectiveLinePowerDegree e d (e * d)) ≃
        projectiveLineQuotientComponent F ((e * d) + (e * d)) :=
    { toFun := fun z => ⟨z.1, by simpa [hdeg] using z.2⟩
      invFun := fun z => ⟨z.1, by simpa [hdeg] using z.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  have hcast : Function.Bijective ecast := ecast.bijective
  have hc := hcast.comp h
  convert hc using 1
  funext x
  apply Subtype.ext
  change (projectiveLinePowerMultiplication F G e d hG x).1 =
    (ecast (projectiveLinePowerMultiplicationAt F G e d (e * d) hG x)).1
  simp [ecast, projectiveLinePowerMultiplicationAt, projectiveLinePowerMultiplication,
    projectiveLinePowerElement, projectiveLineComponentProductLeft,
    projectiveLineHomogeneousElement, projectiveLineMultiplication, mul_comm]

/- The following structure records the output of the source's transported
   multiplication.  The ring and algebra structures are fields so the
   construction does not install a competing global instance on the
   component subtype. -/
structure ProjectiveLineFiniteAlgebraConstruction
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hG : G.IsHomogeneous e) where
  ring : CommRing (projectiveLineQuotientComponent F (e * d) : Type u)
  algebra : letI := ring
    Algebra R (projectiveLineQuotientComponent F (e * d) : Type u)
  finite_locally_free :
    Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
      (projectiveLineQuotientComponent F (e * d) : Type u) d
  ring_add_eq_component_add :
    letI := ring
    ∀ H₁ H₂,
      (H₁ + H₂ : projectiveLineQuotientComponent F (e * d)).1 = H₁.1 + H₂.1
  ring_zero_eq_component_zero :
    letI := ring
    (0 : projectiveLineQuotientComponent F (e * d)).1 = 0
  ring_neg_eq_component_neg :
    letI := ring
    ∀ H, (-H : projectiveLineQuotientComponent F (e * d)).1 = -H.1
  algebra_smul_eq_component_smul :
    letI := ring
    letI := algebra
    ∀ (r : R) (H : projectiveLineQuotientComponent F (e * d)),
      (r • H : projectiveLineQuotientComponent F (e * d)).1 = r • H.1
  multiplication :
    projectiveLineQuotientComponent F (e * d) →
      projectiveLineQuotientComponent F (e * d) →
        projectiveLineQuotientComponent F (e * d)
  one : projectiveLineQuotientComponent F (e * d)
  multiplication_eq_ring_mul :
    letI := ring
    ∀ H₁ H₂, multiplication H₁ H₂ = H₁ * H₂
  one_eq_ring_one :
    letI := ring
    one = 1
  multiplication_rule :
    ∀ H₁ H₂ H₃,
      multiplication H₁ H₂ = H₃ ↔
        (projectiveLinePowerElement F G e d hG).1 * H₃.1 = H₁.1 * H₂.1
  one_eq_power : one = projectiveLinePowerElement F G e d hG

theorem projectiveLine_finite_algebra_construction
    {R : Type u} [CommRing R] (F G : BinaryPolynomial R)
    (d e : ℕ) (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hstart : d ≤ e * d)
    (hfinite : ∀ n : ℕ, d ≤ n →
      Formalization.Books.Algebra.Unit78.FiniteLocallyFreeOfRank R
        (projectiveLineQuotientComponent F n : Type u) d)
    (hmul : ∀ n : ℕ, d ≤ n →
      Function.Bijective (projectiveLineComponentMultiplication F G e n hG)) :
    Nonempty (ProjectiveLineFiniteAlgebraConstruction F G d e hG) := by
  sorry

end

end Formalization.Books.Obsolete.Unit05
