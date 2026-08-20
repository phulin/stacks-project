import Formalization.Books.Algebra.Unit133.FiniteOrderDifferentialOperators
import Formalization.Books.Algebra.Unit148.FormallyUnramifiedMaps
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Commutative Algebra, Chapter 150: Formally étale maps

The formally étale predicate is Mathlib's canonical `RingHom.FormallyEtale`
and `Algebra.FormallyEtale`.  This file records the square-zero lifting,
base-change, infinitesimal, principal-parts, and differential-operator
interfaces from the chapter without introducing a parallel predicate.
-/

namespace Formalization.Books.Algebra.Unit150

open scoped DirectSum TensorProduct
open Formalization.Books.Algebra.Unit133
open Formalization.Books.Algebra.Unit131
open Formalization.Books.Algebra.Unit127

noncomputable section

universe u v

/-! ## Formal étaleness and its elementary permanence properties -/

/-- The source's unique square-zero lifting definition of formal étaleness. -/
theorem formallyEtale_iff_lifting
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) :
    letI : Algebra R S := f.toAlgebra
    f.FormallyEtale ↔
      ∀ ⦃A : Type max u v⦄ [CommRing A] [Algebra R A]
        (I : Ideal A), I ^ 2 = ⊥ →
          Function.Bijective
            ((Ideal.Quotient.mkₐ R I).comp :
              (S →ₐ[R] A) → S →ₐ[R] A ⧸ I) := by
  let : Algebra R S := f.toAlgebra
  exact Algebra.FormallyEtale.iff_comp_bijective

/-- Formal étaleness is equivalent to formal smoothness and formal
unramifiedness, in the order used in the source. -/
theorem formallyEtale_iff_formallySmooth_and_formallyUnramified
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    Algebra.FormallyEtale R S ↔
      Algebra.FormallySmooth R S ∧ Algebra.FormallyUnramified R S := by
  simpa [and_comm] using
    (Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth
      (R := R) (A := S))

/-- Formal étaleness is stable under arbitrary base change. -/
theorem formallyEtale_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R']
    (h : Algebra.FormallyEtale R S) :
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    Algebra.FormallyEtale R' (R' ⊗[R] S) := by
  let : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  let : Algebra.FormallyEtale R S := h
  infer_instance

/-- For a ring map of finite presentation, formal étaleness is equivalent to
étaleness. -/
theorem formallyEtale_iff_etale_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hfp : f.FinitePresentation) :
    f.FormallyEtale ↔ f.Etale := by
  let : Algebra R S := f.toAlgebra
  change Algebra.FormallyEtale R S ↔ Algebra.Etale R S
  constructor
  · intro h
    exact { formallyEtale := h, finitePresentation := hfp }
  · intro h
    exact h.formallyEtale

/-- A directed colimit of formally étale algebras is formally étale. -/
theorem formallyEtale_directedColimit
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (D : DirectedAlgebraColimit f)
    (_h : ∀ i,
      letI : Preorder D.index := D.indexPreorder
      RingHom.FormallyEtale (D.diagram.obj i).hom.hom) :
    f.FormallyEtale := by
  sorry

/-- Every localization map is formally étale. -/
theorem formallyEtale_localization
    {R : Type u} [CommRing R] (M : Submonoid R) :
    (algebraMap R (Localization M)).FormallyEtale := by
  rw [RingHom.formallyEtale_algebraMap]
  exact Algebra.FormallyEtale.of_isLocalization M

/-! ## Infinitesimal lifting and associated graded rings -/

/-- The kernel of the map `R → S/J` in the infinitesimal lifting lemma. -/
def infinitesimalKernel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S) : Ideal R :=
  J.comap f

theorem infinitesimalKernel_eq_quotient_kernel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S) :
    infinitesimalKernel f J =
      RingHom.ker ((Ideal.Quotient.mk J).comp f) := by
  ext r
  simp [infinitesimalKernel, Ideal.Quotient.eq_zero_iff_mem]

/-- The canonical map on the infinitesimal quotients. -/
def infinitesimalQuotientMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S) (n : ℕ) :
    R ⧸ (infinitesimalKernel f J) ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (by
    refine (Ideal.map_le_iff_le_comap).mp ?_
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_comap_le (f := f) (K := J)) n)

/-- The `n`th associated-graded piece of an ideal filtration. -/
abbrev submoduleQuotient
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (P Q : Submodule R M) : Type _ :=
  HasQuotient.Quotient (P : Type _) (Q.comap P.subtype)

/-- The degree-`n` component `I^n/I^(n+1)` of the associated graded ring. -/
abbrev associatedGradedPiece
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) : Type u :=
  submoduleQuotient (I ^ n : Submodule R R) (I ^ (n + 1) : Submodule R R)

/-- The external direct sum of the associated-graded pieces. -/
abbrev associatedGraded
    {R : Type u} [CommRing R] (I : Ideal R) : Type u :=
  DirectSum ℕ (associatedGradedPiece I)

lemma associatedGraded_mul_mem
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ}
    (x : (I ^ n : Submodule R R)) (y : (I ^ m : Submodule R R)) :
    (x : R) * y ∈ I ^ (n + m) := by
  rw [Ideal.IsTwoSided.pow_add]
  exact Ideal.mul_mem_mul x.property y.property

lemma associatedGraded_mul_mem_succ_left
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ}
    (x : (I ^ (n + 1) : Submodule R R)) (y : (I ^ m : Submodule R R)) :
    (x : R) * y ∈ I ^ (n + m + 1) := by
  have h : (x : R) * y ∈ I ^ (n + 1) * I ^ m :=
    Ideal.mul_mem_mul x.property y.property
  rw [← Ideal.IsTwoSided.pow_add] at h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

lemma associatedGraded_mul_mem_succ_right
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ}
    (x : (I ^ n : Submodule R R)) (y : (I ^ (m + 1) : Submodule R R)) :
    (x : R) * y ∈ I ^ (n + m + 1) := by
  have h : (x : R) * y ∈ I ^ n * I ^ (m + 1) :=
    Ideal.mul_mem_mul x.property y.property
  rw [← Ideal.IsTwoSided.pow_add] at h
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private def associatedGradedPieceMulMap
    {R : Type u} [CommRing R] (I : Ideal R) (n m : ℕ) :
    associatedGradedPiece I n →ₗ[R]
      associatedGradedPiece I m →ₗ[R] associatedGradedPiece I (n + m) := by
  let f : (I ^ n : Submodule R R) →ₗ[R]
      (I ^ m : Submodule R R) →ₗ[R] associatedGradedPiece I (n + m) :=
    { toFun := fun x =>
        { toFun := fun y =>
            Submodule.Quotient.mk
              ⟨(x : R) * y, associatedGraded_mul_mem I x y⟩
          map_add' := by
            intro y z
            apply congrArg Submodule.Quotient.mk
            apply Subtype.ext
            simp [mul_add]
          map_smul' := by
            intro r y
            apply congrArg Submodule.Quotient.mk
            apply Subtype.ext
            simp [smul_eq_mul, mul_left_comm] }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp [add_mul]
      map_smul' := by
        intro r x
        apply LinearMap.ext
        intro y
        apply congrArg Submodule.Quotient.mk
        apply Subtype.ext
        simp [smul_eq_mul, mul_assoc] }
  refine LinearMap.liftQ₂ (R := R) (R₂ := R) (S := R) (S₂ := R)
    (ρ := RingHom.id R) (σ := RingHom.id R)
    (Submodule.comap ((I ^ n : Submodule R R).subtype)
      (I ^ (n + 1) : Submodule R R))
    (Submodule.comap ((I ^ m : Submodule R R).subtype)
      (I ^ (m + 1) : Submodule R R)) f ?_ ?_
  · intro x hx
    change x.1 ∈ I ^ (n + 1) at hx
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    change (Submodule.Quotient.mk
      (p := Submodule.comap ((I ^ (n + m) : Submodule R R).subtype)
        (I ^ (n + m + 1) : Submodule R R))
      ⟨x.1 * y.1, associatedGraded_mul_mem I x y⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change x.1 * y.1 ∈ I ^ (n + m + 1)
    exact associatedGraded_mul_mem_succ_left I ⟨x, hx⟩ y
  · intro y hy
    change y.1 ∈ I ^ (m + 1) at hy
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro x
    change (Submodule.Quotient.mk
      (p := Submodule.comap ((I ^ (n + m) : Submodule R R).subtype)
        (I ^ (n + m + 1) : Submodule R R))
      ⟨x.1 * y.1, associatedGraded_mul_mem I x y⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change x.1 * y.1 ∈ I ^ (n + m + 1)
    exact associatedGraded_mul_mem_succ_right I x ⟨y, hy⟩

/-- The canonical product of the degreewise ideal-power quotients. -/
noncomputable def associatedGradedPieceMul
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ} :
    associatedGradedPiece I n → associatedGradedPiece I m →
      associatedGradedPiece I (n + m) :=
  fun x y => associatedGradedPieceMulMap I n m x y

noncomputable def associatedGradedPieceOne
    {R : Type u} [CommRing R] (I : Ideal R) : associatedGradedPiece I 0 :=
  Submodule.Quotient.mk ⟨1, by simp⟩

noncomputable def associatedGradedPieceNatCast
    {R : Type u} [CommRing R] (I : Ideal R) :
    ℕ → associatedGradedPiece I 0 := fun n =>
  Submodule.Quotient.mk ⟨n, by simp⟩

noncomputable def associatedGradedPieceIntCast
    {R : Type u} [CommRing R] (I : Ideal R) :
    ℤ → associatedGradedPiece I 0 := fun n =>
  Submodule.Quotient.mk ⟨n, by simp⟩

@[simp]
lemma associatedGradedPieceMul_mk_mk
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ}
    (x : (I ^ n : Submodule R R)) (y : (I ^ m : Submodule R R)) :
    associatedGradedPieceMul I (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨(x : R) * y, associatedGraded_mul_mem I x y⟩ := by
  simp only [associatedGradedPieceMul, associatedGradedPieceMulMap,
    LinearMap.liftQ₂_mk]
  rfl

private lemma associatedGradedPiece_mk_heq
    {R : Type u} [CommRing R] (I : Ideal R) {n m : ℕ}
    (h : n = m) (x : R) (hx : x ∈ I ^ n) (hy : x ∈ I ^ m) :
    HEq (Submodule.Quotient.mk ⟨x, hx⟩ : associatedGradedPiece I n)
      (Submodule.Quotient.mk ⟨x, hy⟩ : associatedGradedPiece I m) := by
  subst m
  rfl

/-- The canonical graded-ring operations on the associated graded ring. -/
@[instance_reducible]
noncomputable def associatedGradedRing_gcommRingCanonical
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedPiece I) := by
  classical
  letI : GradedMonoid.GOne (associatedGradedPiece I) :=
    ⟨associatedGradedPieceOne I⟩
  letI : GradedMonoid.GMul (associatedGradedPiece I) :=
    ⟨@associatedGradedPieceMul R _ I⟩
  exact {
    mul := @associatedGradedPieceMul R _ I
    mul_zero := by
      intro n m x
      simpa only [associatedGradedPieceMul] using
        (map_zero (associatedGradedPieceMulMap I n m x))
    zero_mul := by
      intro n m x
      change (associatedGradedPieceMulMap I n m 0) x = 0
      simp
    mul_add := by
      intro n m x y z
      simpa only [associatedGradedPieceMul] using
        map_add (associatedGradedPieceMulMap I n m x) y z
    add_mul := by
      intro n m x y z
      change (associatedGradedPieceMulMap I n m (x + y)) z =
        (associatedGradedPieceMulMap I n m x) z +
          (associatedGradedPieceMulMap I n m y) z
      simp
    one := associatedGradedPieceOne I
    one_mul := by
      rintro ⟨n, x⟩
      apply Sigma.ext (zero_add n)
      change HEq (associatedGradedPieceMul I (associatedGradedPieceOne I) x) x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        have hx : (x : R) ∈ I ^ (0 + n) := by
          rw [zero_add]
          exact x.property
        simpa [associatedGradedPieceOne, associatedGradedPieceMul_mk_mk] using
          associatedGradedPiece_mk_heq I (zero_add n) (x : R) hx x.property
    mul_one := by
      rintro ⟨n, x⟩
      apply Sigma.ext (add_zero n)
      change HEq (associatedGradedPieceMul I x (associatedGradedPieceOne I)) x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        simp [associatedGradedPieceOne, associatedGradedPieceMul_mk_mk]
    mul_assoc := by
      rintro ⟨n, x⟩ ⟨m, y⟩ ⟨k, z⟩
      apply Sigma.ext (Nat.add_assoc n m k)
      change HEq
        (associatedGradedPieceMul I
          (associatedGradedPieceMul I x y) z)
        (associatedGradedPieceMul I x
          (associatedGradedPieceMul I y z))
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          induction z using Submodule.Quotient.induction_on with
          | _ z =>
            have hx : (x : R) * ((y : R) * (z : R)) ∈
                I ^ ((n + m) + k) := by
              simpa [mul_assoc] using
                (associatedGraded_mul_mem I
                  ⟨(x : R) * (y : R), associatedGraded_mul_mem I x y⟩ z)
            have hy : (x : R) * ((y : R) * (z : R)) ∈
                I ^ (n + (m + k)) := by
              exact associatedGraded_mul_mem I x
                ⟨(y : R) * (z : R), associatedGraded_mul_mem I y z⟩
            simpa [associatedGradedPieceMul_mk_mk, mul_assoc] using
              associatedGradedPiece_mk_heq I (Nat.add_assoc n m k)
                ((x : R) * ((y : R) * (z : R))) hx hy
    mul_comm := by
      rintro ⟨n, x⟩ ⟨m, y⟩
      apply Sigma.ext (Nat.add_comm n m)
      change HEq (associatedGradedPieceMul I x y)
        (associatedGradedPieceMul I y x)
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          have hx : (x : R) * (y : R) ∈ I ^ (n + m) :=
            associatedGraded_mul_mem I x y
          have hy : (x : R) * (y : R) ∈ I ^ (m + n) := by
            simpa [mul_comm] using (associatedGraded_mul_mem I y x)
          simpa [associatedGradedPieceMul_mk_mk, mul_comm] using
            associatedGradedPiece_mk_heq I (Nat.add_comm n m)
              ((x : R) * (y : R)) hx hy
    natCast := associatedGradedPieceNatCast I
    natCast_zero := by
      simp [associatedGradedPieceNatCast]
    natCast_succ := by
      intro n
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp
    intCast := associatedGradedPieceIntCast I
    intCast_ofNat := by
      intro n
      simp [associatedGradedPieceIntCast, associatedGradedPieceNatCast]
    intCast_negSucc_ofNat := by
      intro n
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp
  }

theorem associatedGradedRing_gcommRing_exists
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty (DirectSum.GCommRing (associatedGradedPiece I)) :=
  ⟨associatedGradedRing_gcommRingCanonical I⟩

noncomputable instance associatedGradedRing_gcommRing
    {R : Type u} [CommRing R] (I : Ideal R) :
    DirectSum.GCommRing (associatedGradedPiece I) :=
  associatedGradedRing_gcommRingCanonical I

/-- The degree-`n` component of the associated graded module of an `R`-module.
The quotient is taken in the submodule `I^n • ⊤`, as in the corresponding
associated-graded ring piece. -/
abbrev associatedGradedModulePiece
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (n : ℕ) : Type _ :=
  submoduleQuotient (I ^ n • (⊤ : Submodule R M))
    (I ^ (n + 1) • (⊤ : Submodule R M))

private theorem associatedGradedModulePiece_mk_heq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ} (h : i = j)
    (a : ((I ^ i : Submodule R R) • (⊤ : Submodule R M) : Submodule R M))
    (b : ((I ^ j : Submodule R R) • (⊤ : Submodule R M) : Submodule R M))
    (hab : (a : M) = (b : M)) :
    HEq (Submodule.Quotient.mk a : associatedGradedModulePiece (M := M) I i)
      (Submodule.Quotient.mk b : associatedGradedModulePiece (M := M) I j) := by
  apply heq_of_eqRec_eq
    (congrArg (fun n => associatedGradedModulePiece (M := M) I n) h)
  cases h
  apply congrArg (fun z : ((I ^ i : Submodule R R) • (⊤ : Submodule R M) : Submodule R M) =>
    (Submodule.Quotient.mk z : associatedGradedModulePiece (M := M) I i))
  apply Subtype.ext
  exact hab

private noncomputable def associatedGradedModule_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : {i j : ℕ} → associatedGradedPiece I i →
      associatedGradedModulePiece (M := M) I j →
        associatedGradedModulePiece (M := M) I (i + j) := by
  intro i j a b
  refine Quotient.liftOn₂' a b (fun x y =>
    Submodule.Quotient.mk ⟨(x : R) • (y : M), ?_⟩) ?_
  · have h := Submodule.smul_mem_smul x.property y.property
    rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
      ← Ideal.IsTwoSided.pow_add] at h
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · intro a₁ a₂ b₁ b₂ ha hb
    apply (Submodule.Quotient.eq _).2
    rw [Submodule.quotientRel_def] at ha hb
    change (a₁ : R) - (b₁ : R) ∈ I ^ (i + 1) at ha
    change (a₂ : M) - (b₂ : M) ∈ I ^ (j + 1) • (⊤ : Submodule R M) at hb
    change (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) ∈
      I ^ (i + j + 1) • (⊤ : Submodule R M)
    have h₁ : ((a₁ : R) - (b₁ : R)) • (a₂ : M) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M) := by
      have h := Submodule.smul_mem_smul ha a₂.property
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
        ← Ideal.IsTwoSided.pow_add] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    have h₂ : (b₁ : R) • ((a₂ : M) - (b₂ : M)) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M) := by
      have h := Submodule.smul_mem_smul b₁.property hb
      rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
        ← Ideal.IsTwoSided.pow_add] at h
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    rw [show (a₁ : R) • (a₂ : M) - (b₁ : R) • (b₂ : M) =
        ((a₁ : R) - (b₁ : R)) • (a₂ : M) +
          (b₁ : R) • ((a₂ : M) - (b₂ : M)) by
        simp only [sub_smul, smul_sub]
        abel]
    exact Submodule.add_mem _ h₁ h₂

private theorem associatedGradedModule_smul_mk
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {i j : ℕ}
    (a : (I ^ i : Submodule R R))
    (b : ((I ^ j : Submodule R R) • (⊤ : Submodule R M) : Submodule R M)) :
    associatedGradedModule_smul I (Submodule.Quotient.mk a)
      (Submodule.Quotient.mk b) =
      (Submodule.Quotient.mk ⟨(a : R) • (b : M), by
        have h := Submodule.smul_mem_smul a.property b.property
        rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
          ← Ideal.IsTwoSided.pow_add] at h
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h⟩ :
        associatedGradedModulePiece (M := M) I (i + j) := by
  simp [associatedGradedModule_smul, Submodule.Quotient.mk]

@[reducible] private noncomputable def associatedGradedModule_gmulAction
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) : GradedMonoid.GMulAction (associatedGradedPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) := by
  let one : associatedGradedPiece I 0 :=
    Submodule.Quotient.mk ⟨1, by simp⟩
  let gsmul : GradedMonoid.GSMul (associatedGradedPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { smul := associatedGradedModule_smul I }
  exact {
    toGSMul := gsmul
    one_smul := by
      rintro ⟨j, b⟩
      change GradedMonoid.mk 0 one • GradedMonoid.mk j b = _
      apply Sigma.ext (zero_add j)
      refine Submodule.Quotient.induction_on _ b ?_
      intro y
      change HEq (associatedGradedModule_smul I (i := 0) (j := j) one
          (Submodule.Quotient.mk y)) (Submodule.Quotient.mk y)
      rw [associatedGradedModule_smul_mk]
      exact associatedGradedModulePiece_mk_heq I (zero_add j)
        (⟨(1 : R) • (y : M), by
          have h := Submodule.smul_mem_smul
            (show (1 : R) ∈ (I ^ 0 : Submodule R R) by simp) y.property
          rw [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add] at h
          simp only [one_smul, zero_add] at h ⊢
          exact h⟩)
        (⟨(y : M), y.property⟩) (by simp)
    mul_smul := by
      rintro ⟨i, a⟩ ⟨j, a'⟩ ⟨k, b⟩
      change (GradedMonoid.mk i a * GradedMonoid.mk j a') •
          GradedMonoid.mk k b =
        GradedMonoid.mk i a • (GradedMonoid.mk j a' • GradedMonoid.mk k b)
      apply Sigma.ext (add_assoc i j k)
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ a' ?_
      intro a'
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      change HEq
        (associatedGradedModule_smul I (i := i + j) (j := k)
          (associatedGradedPieceMul I
            (Submodule.Quotient.mk a) (Submodule.Quotient.mk a'))
          (Submodule.Quotient.mk b))
        (associatedGradedModule_smul I (i := i) (j := j + k)
          (Submodule.Quotient.mk a)
          (associatedGradedModule_smul I (i := j) (j := k)
            (Submodule.Quotient.mk a') (Submodule.Quotient.mk b)))
      rw [associatedGradedPieceMul_mk_mk]
      rw [associatedGradedModule_smul_mk, associatedGradedModule_smul_mk,
        associatedGradedModule_smul_mk]
      exact associatedGradedModulePiece_mk_heq I (add_assoc i j k)
        (⟨((a : R) * (a' : R)) • (b : M), by
          have h := Submodule.smul_mem_smul
            (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
              rw [Ideal.IsTwoSided.pow_add]
              exact Ideal.mul_mem_mul a.property a'.property) b.property
          simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using h⟩)
        (⟨(a : R) • ((a' : R) • (b : M)), by
          have h := Submodule.smul_mem_smul
            (show (a : R) * (a' : R) ∈ (I ^ (i + j) : Submodule R R) by
              rw [Ideal.IsTwoSided.pow_add]
              exact Ideal.mul_mem_mul a.property a'.property) b.property
          simpa [← Submodule.smul_assoc, Ideal.smul_eq_mul,
            ← Ideal.IsTwoSided.pow_add, smul_smul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using h⟩)
        (by
          change ((a : R) * (a' : R)) • (b : M) =
            (a : R) • ((a' : R) • (b : M))
          rw [smul_smul]) }

/-- The canonical graded-module structure on the associated graded module. -/
@[instance_reducible]
noncomputable def associatedGradedModule_gmoduleCanonical
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    DirectSum.Gmodule (associatedGradedPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) := by
  let gmulAction := associatedGradedModule_gmulAction I
  let gdistrib : DirectSum.GdistribMulAction (associatedGradedPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n) :=
    { toGMulAction := gmulAction
      smul_add := by
        have hsmul : gmulAction.toGSMul =
            ({ smul := associatedGradedModule_smul I } :
              GradedMonoid.GSMul (associatedGradedPiece I)
                (fun n => associatedGradedModulePiece (M := M) I n)) := by
          rfl
        intro i j a b c
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        refine Submodule.Quotient.induction_on _ b ?_
        intro b
        refine Submodule.Quotient.induction_on _ c ?_
        intro c
        rw [← Submodule.Quotient.mk_add]
        rw [hsmul]
        change associatedGradedModule_smul I (Submodule.Quotient.mk a)
            (Submodule.Quotient.mk (b + c)) =
          associatedGradedModule_smul I (Submodule.Quotient.mk a)
              (Submodule.Quotient.mk b) +
            associatedGradedModule_smul I (Submodule.Quotient.mk a)
              (Submodule.Quotient.mk c)
        apply (Submodule.Quotient.eq _).2
        change (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) ∈
          I ^ (i + j + 1) • (⊤ : Submodule R M)
        rw [show (a : R) • ((b : M) + (c : M)) -
            ((a : R) • (b : M) + (a : R) • (c : M)) = 0 by
          rw [smul_add, sub_self]]
        exact Submodule.zero_mem _
      smul_zero := by
        intro i j a
        refine Submodule.Quotient.induction_on _ a ?_
        intro a
        simp [Submodule.Quotient.mk]
        apply (Submodule.Quotient.mk_eq_zero _).2
        simp }
  exact { gdistrib with
    smul := fun {i j} => associatedGradedModule_smul I
    add_smul := by
      intro i j a a' b
      refine Submodule.Quotient.induction_on _ a ?_
      intro a
      refine Submodule.Quotient.induction_on _ a' ?_
      intro a'
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      rw [← Submodule.Quotient.mk_add]
      rw [associatedGradedModule_smul_mk, associatedGradedModule_smul_mk,
        associatedGradedModule_smul_mk]
      apply (Submodule.Quotient.eq _).2
      change ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) ∈
        I ^ (i + j + 1) • (⊤ : Submodule R M)
      rw [show ((a : R) + (a' : R)) • (b : M) -
          ((a : R) • (b : M) + (a' : R) • (b : M)) = 0 by
        rw [add_smul, sub_self]]
      exact Submodule.zero_mem _
    zero_smul := by
      intro i j b
      refine Submodule.Quotient.induction_on _ b ?_
      intro b
      simp [associatedGradedModule_smul, Submodule.Quotient.mk]
      apply (Submodule.Quotient.mk_eq_zero _).2
      simp }

theorem associatedGradedModule_gmodule_exists
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    Nonempty (DirectSum.Gmodule (associatedGradedPiece I)
      (fun n => associatedGradedModulePiece (M := M) I n)) :=
  ⟨associatedGradedModule_gmoduleCanonical I⟩

/-- A graded ring equivalence between two external associated-graded rings.
The component maps and the homogeneous-component equation retain the grading
that is implicit in the textbook's displayed graded-ring isomorphism. -/
structure AssociatedGradedRingEquivalence
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) where
  equiv : associatedGraded I ≃+* associatedGraded J
  component : ∀ n, associatedGradedPiece I n →+ associatedGradedPiece J n
  equiv_homogeneous : ∀ (n : ℕ) (x : associatedGradedPiece I n),
    equiv (DirectSum.of (associatedGradedPiece I) n x) =
      DirectSum.of (associatedGradedPiece J) n (component n x)

/-- Formal étaleness identifies all infinitesimal quotients and their
associated graded rings. -/
theorem formallyEtale_lift_infinitesimal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S)
    (_hquot : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (_hf : f.FormallyEtale) :
    (∀ n, Function.Bijective (infinitesimalQuotientMap f J n)) ∧
      Nonempty (AssociatedGradedRingEquivalence
        (infinitesimalKernel f J) J) := by
  sorry

/-- The isomorphisms on infinitesimal quotients obtained from the canonical
maps in `formallyEtale_lift_infinitesimal`. -/
noncomputable def infinitesimalQuotientEquiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S)
    (n : ℕ) (h : Function.Bijective (infinitesimalQuotientMap f J n)) :
    R ⧸ (infinitesimalKernel f J) ^ n ≃+* S ⧸ J ^ n :=
  RingEquiv.ofBijective (infinitesimalQuotientMap f J n) h

theorem formallyEtale_lift_infinitesimal_equiv
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S)
    (hquot : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (hf : f.FormallyEtale) :
    ∀ n, Nonempty
      (R ⧸ (infinitesimalKernel f J) ^ n ≃+* S ⧸ J ^ n) := by
  intro n
  exact ⟨infinitesimalQuotientEquiv f J n
    ((formallyEtale_lift_infinitesimal f J hquot hf).1 n)⟩

/-! ## Diagonal powers, differentials, and principal parts -/

/-- The diagonal-power quotient is the displayed quotient in the source's
principal-parts argument. -/
theorem formallyEtale_omega
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    (_hf : Algebra.FormallyEtale S S') (k : ℕ) :
    letI : Algebra S (S ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    letI : Algebra S' (S' ⊗[S]
      ((S ⊗[R] S) ⧸ (Unit133.diagonalIdeal (R := R) (S := S)) ^ (k + 1))) :=
        Algebra.TensorProduct.leftAlgebra
    letI : Algebra S' (S' ⊗[R] S') := Algebra.TensorProduct.leftAlgebra
    Nonempty
      ((S' ⊗[S]
          ((S ⊗[R] S) ⧸ (Unit133.diagonalIdeal (R := R) (S := S)) ^ (k + 1)))
        ≃ₐ[S']
        ((S' ⊗[R] S') ⧸
          (Unit133.diagonalIdeal (R := R) (S := S')) ^ (k + 1))) := by
  sorry

/-- Base change of Kähler differentials along a formally étale map. -/
theorem formallyEtale_omega_differentials
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    (hf : Algebra.FormallyEtale S S') :
    Nonempty (S' ⊗[S] ModuleOfDifferentials R S ≃ₗ[S']
      ModuleOfDifferentials R S') := by
  let : Algebra.FormallyEtale S S' := hf
  exact ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'⟩

/-- The module used after base change in the principal-parts lemma. -/
abbrev principalPartsBaseChangeModule
    {S S' : Type u} (M : Type u) [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra S S'] [Module S M] := S' ⊗[S] M

/-- Base change of every module of principal parts along a formally étale map. -/
theorem formallyEtale_principalParts
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (_hf : Algebra.FormallyEtale S S') (k : ℕ) :
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      TensorProduct.leftModule
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
    Nonempty
      (S' ⊗[S] PrincipalParts (R := R) (S := S) (M := M) k ≃ₗ[S']
        PrincipalParts (R := R) (S := S')
          (M := principalPartsBaseChangeModule (S := S) (S' := S') M) k) := by
  sorry

/-! ## Differential-operator extensions and their composition -/

/-- The canonical map from a module into its scalar extension. -/
def principalPartsBaseChangeMap
    {S S' M : Type u} [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra S S'] [Module S M] :
    M → principalPartsBaseChangeModule (S := S) (S' := S') M :=
  fun m => 1 ⊗ₜ[S] m

/-- Every finite-order differential operator has a unique extension to the
scalar-extended modules, of the same (hence no greater) order. -/
theorem formallyEtale_differentialOperator_extension
    {R S S' M N : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (_hf : Algebra.FormallyEtale S S') (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      TensorProduct.leftModule
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      TensorProduct.leftModule
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
    ∃! E : DifferentialOperator (R := R) (S := S')
        (M := principalPartsBaseChangeModule (S := S) (S' := S') M)
        (N := principalPartsBaseChangeModule (S := S) (S' := S') N) k,
    ∀ m, E.1 (principalPartsBaseChangeMap (S := S) (S' := S') m) =
        principalPartsBaseChangeMap (S := S) (S' := S') (D.1 m) := by
  sorry

/-- The unique extension supplied by
`formallyEtale_differentialOperator_extension`. -/
noncomputable def formallyEtale_differentialOperatorExtension
    {R S S' M N : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (_hf : Algebra.FormallyEtale S S') (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      TensorProduct.leftModule
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      TensorProduct.leftModule
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s n
          simp
        · intro x y hx hy
          simp [hx, hy]
    DifferentialOperator (R := R) (S := S')
      (M := principalPartsBaseChangeModule (S := S) (S' := S') M)
      (N := principalPartsBaseChangeModule (S := S) (S' := S') N) k := by
  exact Classical.choose (formallyEtale_differentialOperator_extension _hf k D)

theorem formallyEtale_differentialOperatorExtension_spec
    {R S S' M N : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    (_hf : Algebra.FormallyEtale S S') (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      TensorProduct.leftModule
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      TensorProduct.leftModule
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
    letI : IsScalarTower R S'
        (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
      by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s n
          simp
        · intro x y hx hy
          simp [hx, hy]
    ∀ m, (formallyEtale_differentialOperatorExtension _hf k D).1
        (principalPartsBaseChangeMap (S := S) (S' := S') m) =
      principalPartsBaseChangeMap (S := S) (S' := S') (D.1 m) := by
  exact (Classical.choose_spec
    (formallyEtale_differentialOperator_extension _hf k D)).1

/-- Extensions of two finite-order differential operators compose to the
extension of their composite. -/
theorem formallyEtale_differentialOperator_comp_extension
    {R S S' M N L : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module S M] [Module S N] [Module S L]
    [Module R M] [Module R N] [Module R L]
    [IsScalarTower R S M] [IsScalarTower R S N] [IsScalarTower R S L]
    (_hf : Algebra.FormallyEtale S S') (k₁ k₂ : ℕ)
    (D₁ : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k₁)
    (D₂ : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k₂)
    : letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
        TensorProduct.leftModule
      letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N) :=
        TensorProduct.leftModule
      letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') L) :=
        TensorProduct.leftModule
      letI : IsScalarTower R S'
          (principalPartsBaseChangeModule (S := S) (S' := S') M) := by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
      letI : IsScalarTower R S'
          (principalPartsBaseChangeModule (S := S) (S' := S') N) := by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
      letI : IsScalarTower R S'
          (principalPartsBaseChangeModule (S := S) (S' := S') L) := by
        refine IsScalarTower.of_algebraMap_smul ?_
        intro r x
        refine TensorProduct.induction_on x ?_ ?_ ?_
        · simp
        · intro s m
          simp
        · intro x y hx hy
          simp [hx, hy]
      ∀ (E₁ : DifferentialOperator (R := R) (S := S')
          (M := principalPartsBaseChangeModule (S := S) (S' := S') M)
          (N := principalPartsBaseChangeModule (S := S) (S' := S') N) k₁)
        (E₂ : DifferentialOperator (R := R) (S := S')
          (M := principalPartsBaseChangeModule (S := S) (S' := S') N)
          (N := principalPartsBaseChangeModule (S := S) (S' := S') L) k₂),
        (∀ m, E₁.1 (principalPartsBaseChangeMap (S := S) (S' := S') m) =
          principalPartsBaseChangeMap (S := S) (S' := S') (D₁.1 m)) →
        (∀ n, E₂.1 (principalPartsBaseChangeMap (S := S) (S' := S') n) =
          principalPartsBaseChangeMap (S := S) (S' := S') (D₂.1 n)) →
        ∀ m, (differentialOperatorComp E₂ E₁).1
            (principalPartsBaseChangeMap (S := S) (S' := S') m) =
          principalPartsBaseChangeMap (S := S) (S' := S') (D₂.1 (D₁.1 m)) := by
  sorry

/- The source's final module-action sentence is accounted for by the preceding
composition theorem together with `differentialOperatorComp`: the earlier
chapter deliberately represents finite-order operators as the filtered
submodules `DifferentialOperator`, rather than introducing a second
all-orders differential-operator algebra here. -/

end

end Formalization.Books.Algebra.Unit150
