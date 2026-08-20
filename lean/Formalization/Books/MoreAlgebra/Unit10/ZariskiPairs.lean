import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.Integral
import Formalization.Books.Algebra.Unit32.LocallyNilpotent
import Formalization.Books.Algebra.Unit138.FormallySmoothMaps
import Formalization.Books.Algebra.Unit61.ApplicationsDimensionTheory
import Formalization.Books.MoreAlgebra.Unit03.StablyFree
import Formalization.Books.MoreAlgebra.Unit09.Lifting

/-!
# More on Algebra, Chapter 10: Zariski pairs

This file records the pair conventions and the theorem interfaces in the
section on Zariski pairs.  Quotients, idempotents, finiteness properties of
ring maps, and Jacobson rings use the canonical Mathlib constructions.
-/

namespace Formalization.Books.MoreAlgebra.Unit10

open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Pairs and the Zariski-pair condition -/

/-- A pair `(A, I)` consisting of a commutative ring and an ideal of it. -/
structure Pair (A : Type u) [CommRing A] where
  ideal : Ideal A

/-- A morphism of pairs is a ring map carrying the source ideal into the
target ideal.  `Ideal.map` is equivalent to the elementwise containment used
in the source because the target is an ideal. -/
def PairHom {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (P : Pair A) (Q : Pair B) (f : A →+* B) : Prop :=
  Ideal.map f P.ideal ≤ Q.ideal

/-- The condition that the distinguished ideal of a pair is contained in the
Jacobson radical. -/
def ZariskiPair {A : Type u} [CommRing A] (P : Pair A) : Prop :=
  P.ideal ≤ Ring.jacobson A

/-! ## Idempotents modulo a Jacobson-radical ideal -/

private theorem isUnit_one_add_of_mem_jacobson
    {A : Type u} [CommRing A] {x : A} (hx : x ∈ Ring.jacobson A) :
    IsUnit (1 + x) := by
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  rw [Ideal.jacobson_bot]
  simpa [sub_eq_add_neg, add_assoc] using hx

/-- Idempotents are determined by their reductions modulo a Jacobson-radical
ideal. -/
theorem idempotents_determined_modulo_radical
    {A : Type u} [CommRing A] (P : Pair A) (hP : ZariskiPair P) :
    Function.Injective
      (Formalization.Books.Algebra.Unit32.quotientIdempotentMap P.ideal) := by
  intro e₁ e₂ he
  apply Subtype.ext
  have h' :
      Ideal.Quotient.mk P.ideal e₁.1 =
        Ideal.Quotient.mk P.ideal e₂.1 := by
    simpa [Formalization.Books.Algebra.Unit32.quotientIdempotentMap] using
      congrArg Subtype.val he
  have hdmem : e₁.1 - e₂.1 ∈ P.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, h', sub_self]
  change P.ideal ≤ Ring.jacobson A at hP
  have hd : e₁.1 - e₂.1 ∈ Ring.jacobson A := hP hdmem
  let d : A := e₁.1 - e₂.1
  have hunit_add : IsUnit (1 + d) := by
    simpa [d] using isUnit_one_add_of_mem_jacobson hd
  have hunit_sub : IsUnit (1 - d) := by
    simpa [sub_eq_add_neg] using
      isUnit_one_add_of_mem_jacobson (x := -d) ((Ring.jacobson A).neg_mem hd)
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hunit_sub
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp hunit_add
  have hzero : d * (1 - d) * (1 + d) = 0 := by
    have hc :=
      Formalization.Books.Algebra.Unit32.idempotent_sub_cube_eq
        e₁.property e₂.property
    dsimp [d]
    calc
      (e₁.1 - e₂.1) * (1 - (e₁.1 - e₂.1)) *
          (1 + (e₁.1 - e₂.1)) =
          (e₁.1 - e₂.1) - (e₁.1 - e₂.1) ^ 3 := by ring
      _ = 0 := by rw [hc]; ring
  have hd0 : d = 0 := by
    calc
      d = 1 * d * 1 := by simp
      _ = ((1 - d) * u) * d * ((1 + d) * v) := by rw [hu, hv]
      _ = (d * (1 - d) * (1 + d)) * (u * v) := by ring
      _ = 0 := by rw [hzero, zero_mul]
  exact sub_eq_zero.mp (by simpa [d] using hd0)

private theorem surjective_of_quotient_eq_of_le_jacobson_bot
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    {X : Type v} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (g : X →ₗ[R] X)
    (hg : ∀ x : X, (I • (⊤ : Submodule R X)).mkQ (g x) =
      (I • (⊤ : Submodule R X)).mkQ x) : Function.Surjective g := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI
  intro x hx
  have hzero : (I • (⊤ : Submodule R X)).mkQ (x - g x) = 0 := by
    rw [map_sub, hg x, sub_self]
  have hmem : x - g x ∈ I • (⊤ : Submodule R X) := by
    exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R X))).mp hzero
  rw [← sub_add_cancel x (g x)]
  exact Submodule.add_mem _
    ((le_sup_right : I • (⊤ : Submodule R X) ≤
      LinearMap.range g ⊔ I • (⊤ : Submodule R X)) hmem)
    ((le_sup_left : LinearMap.range g ≤
      LinearMap.range g ⊔ I • (⊤ : Submodule R X)) ⟨x, rfl⟩)

private theorem finiteProjective_map_isIso_of_inducesQuotientEquiv'
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I ≤ Ring.jacobson R)
    {M : Type u} {N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (φ : M →ₗ[R] N)
    (hφ : ∃ e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I]
        (N ⧸ (I • (⊤ : Submodule R N))),
      ∀ x : M,
        e ((I • (⊤ : Submodule R M)).mkQ x) =
          (I • (⊤ : Submodule R N)).mkQ (φ x)) :
    ∃ e : M ≃ₗ[R] N, e.toLinearMap = φ := by
  classical
  obtain ⟨e, he⟩ := hφ
  let q : M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    (I • (⊤ : Submodule R M)).mkQ
  let q' : N →ₗ[R] (N ⧸ (I • (⊤ : Submodule R N))) :=
    (I • (⊤ : Submodule R N)).mkQ
  let eR : (N ⧸ (I • (⊤ : Submodule R N))) →ₗ[R]
      (M ⧸ (I • (⊤ : Submodule R M))) :=
    e.symm.toLinearMap.restrictScalars R
  obtain ⟨ψ, hψ⟩ := Module.projective_lifting_property q
    (eR.comp q') (Submodule.mkQ_surjective _)
  have hI' : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    simpa only [Ideal.jacobson_bot] using hI
  have hleft (x : M) : q (ψ (φ x)) = q x := by
    calc
      q (ψ (φ x)) = e.symm (q' (φ x)) := by
        simpa [q, q', eR, LinearMap.comp_apply] using
          congrArg (fun F => F (φ x)) hψ
      _ = e.symm (e (q x)) := by rw [← he x]
      _ = q x := e.symm_apply_apply _
  have hright (y : N) : q' (φ (ψ y)) = q' y := by
    calc
      q' (φ (ψ y)) = e (q (ψ y)) := (he (ψ y)).symm
      _ = e (e.symm (q' y)) := by
        have h := congrArg (fun F => F y) hψ
        simpa [q, q', eR, LinearMap.comp_apply] using congrArg (fun z => e z) h
      _ = q' y := e.apply_symm_apply _
  have hleft_surj : Function.Surjective (ψ.comp φ) :=
    surjective_of_quotient_eq_of_le_jacobson_bot I hI'
      (ψ.comp φ) hleft
  have hright_surj : Function.Surjective (φ.comp ψ) :=
    surjective_of_quotient_eq_of_le_jacobson_bot I hI'
      (φ.comp ψ) hright
  have hleft_bij : Function.Bijective (ψ.comp φ) :=
    OrzechProperty.bijective_of_surjective_endomorphism _ hleft_surj
  have hright_bij : Function.Bijective (φ.comp ψ) :=
    OrzechProperty.bijective_of_surjective_endomorphism _ hright_surj
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply hleft_bij.1
      simp [LinearMap.comp_apply, hxy]
    · intro y
      obtain ⟨x, hx⟩ := hright_surj y
      exact ⟨ψ x, by simpa [LinearMap.comp_apply] using hx⟩
  exact ⟨LinearEquiv.ofBijective φ hφ_bij, rfl⟩

/-! ## Checking an isomorphism from the quotient -/

/-- A flat, integral, finitely presented map which is an isomorphism after
reduction modulo a Zariski-pair ideal is already an isomorphism. -/
theorem check_isomorphism_zariski
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (P : Pair A) (hP : ZariskiPair P)
    (f : A →+* B) (hflat : f.Flat) (hintegral : f.IsIntegral)
    (hfp : f.FinitePresentation)
    (hquot : Function.Bijective
      (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap f P.ideal)) :
    Function.Bijective f := by
  let : Algebra A B := f.toAlgebra
  have hfinite : RingHom.Finite f :=
    hintegral.to_finite (RingHom.FiniteType.of_finitePresentation hfp)
  let : Module.Finite A B := hfinite
  let : Algebra.FinitePresentation A B := hfp
  let : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  let : Module.Flat A B := hflat
  let : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  let : Algebra (A ⧸ P.ideal) (B ⧸ Ideal.map (algebraMap A B) P.ideal) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (p := P.ideal) (P := Ideal.map (algebraMap A B) P.ideal)
      Ideal.le_comap_map
  let eRing : (A ⧸ P.ideal) ≃+* (B ⧸ Ideal.map (algebraMap A B) P.ideal) :=
    RingEquiv.ofBijective
      (Formalization.Books.Algebra.Unit138.quotientBaseChangeRingMap f P.ideal)
      hquot
  let eAlg : (A ⧸ P.ideal) ≃ₐ[A ⧸ P.ideal]
      (B ⧸ Ideal.map (algebraMap A B) P.ideal) :=
    AlgEquiv.ofRingEquiv (f := eRing) (by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl)
  let eA : ((A ⧸ P.ideal) ⊗[A] A) ≃ₗ[A ⧸ P.ideal]
      (A ⧸ (P.ideal • (⊤ : Submodule A A))) :=
    (TensorProduct.quotTensorEquivQuotSMul A P.ideal).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let eB : ((A ⧸ P.ideal) ⊗[A] B) ≃ₗ[A ⧸ P.ideal]
      (B ⧸ (P.ideal • (⊤ : Submodule A B))) :=
    (TensorProduct.quotTensorEquivQuotSMul B P.ideal).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective
  let hmap : Ideal.map (RingHom.id A) P.ideal =
      Ideal.map (algebraMap A A) P.ideal := by simp
  let qA0 : (A ⧸ P.ideal) ≃ₗ[A]
      (A ⧸ Ideal.map (RingHom.id A) P.ideal) :=
    (Ideal.quotientEquivAlgOfEq A P.ideal.map_id).symm.toLinearEquiv
  let qA1 : (A ⧸ Ideal.map (RingHom.id A) P.ideal) ≃ₗ[A]
      (A ⧸ Ideal.map (algebraMap A A) P.ideal) :=
    (Ideal.quotientEquivAlgOfEq A hmap).toLinearEquiv
  let qA : (A ⧸ P.ideal) ≃ₗ[A]
      (A ⧸ Ideal.map (algebraMap A A) P.ideal) := qA0 ≪≫ₗ qA1
  let tA : (A ⧸ Ideal.map (algebraMap A A) P.ideal) ≃ₗ[A]
      ((A ⧸ P.ideal) ⊗[A] A) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A P.ideal).toLinearEquiv
      |>.restrictScalars A
  let eAalg : (A ⧸ P.ideal) ≃ₗ[A ⧸ P.ideal]
      ((A ⧸ P.ideal) ⊗[A] A) := by
    exact (qA ≪≫ₗ tA).extendScalarsOfSurjective
      (R := A) (S := A ⧸ P.ideal) Ideal.Quotient.mk_surjective
  let eQuot : (A ⧸ (P.ideal • (⊤ : Submodule A A))) ≃ₗ[A ⧸ P.ideal]
      (B ⧸ (P.ideal • (⊤ : Submodule A B))) :=
    eA.symm ≪≫ₗ
      eAalg.symm ≪≫ₗ
      eAlg.toLinearEquiv ≪≫ₗ
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P.ideal).toLinearEquiv ≪≫ₗ
      eB
  have hInd : ∀ x : A,
      eQuot ((P.ideal • (⊤ : Submodule A A)).mkQ x) =
        (P.ideal • (⊤ : Submodule A B)).mkQ (Algebra.linearMap A B x) := by
    intro x
    have hA :
        eAalg.symm (eA.symm ((P.ideal • (⊤ : Submodule A A)).mkQ x)) =
          Ideal.Quotient.mk P.ideal x := by
      have hx : eA.symm ((P.ideal • (⊤ : Submodule A A)).mkQ x) =
          (1 : A ⧸ P.ideal) ⊗ₜ[A] x := by
        change (TensorProduct.quotTensorEquivQuotSMul A P.ideal).symm
            (Submodule.Quotient.mk x) = _
        exact TensorProduct.quotTensorEquivQuotSMul_symm_mk P.ideal x
      rw [hx]
      change qA.symm (tA.symm ((1 : A ⧸ P.ideal) ⊗ₜ[A] x)) = _
      apply qA.injective
      simp only [LinearEquiv.apply_symm_apply]
      apply tA.injective
      have hqA : qA (Ideal.Quotient.mk P.ideal x) =
          Ideal.Quotient.mk (Ideal.map (algebraMap A A) P.ideal) x := by
        simp [qA, qA0, qA1]
      rw [hqA]
      rw [tA.apply_symm_apply]
      change (1 : A ⧸ P.ideal) ⊗ₜ[A] x =
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A P.ideal)
          (Ideal.Quotient.mk (Ideal.map (algebraMap A A) P.ideal) x)
      rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
    change (eA.symm ≪≫ₗ eAalg.symm ≪≫ₗ eAlg.toLinearEquiv ≪≫ₗ
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P.ideal).toLinearEquiv ≪≫ₗ
      eB) ((P.ideal • (⊤ : Submodule A A)).mkQ x) = _
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA]
    change eB ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P.ideal)
      (Ideal.Quotient.mk (Ideal.map f P.ideal) (f x))) = _
    change (TensorProduct.quotTensorEquivQuotSMul B P.ideal)
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P.ideal)
        (Ideal.Quotient.mk (Ideal.map f P.ideal) (f x))) = _
    have hq :
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B P.ideal)
            (Ideal.Quotient.mk (Ideal.map f P.ideal) (f x)) =
          (1 : A ⧸ P.ideal) ⊗ₜ[A] f x := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk
          (B := B) (I := P.ideal) (f x))
    rw [hq]
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    rfl
  change P.ideal ≤ Ring.jacobson A at hP
  let hφ : ∃ e : (A ⧸ (P.ideal • (⊤ : Submodule A A))) ≃ₗ[A ⧸ P.ideal]
      (B ⧸ (P.ideal • (⊤ : Submodule A B))),
      ∀ x : A,
        e ((P.ideal • (⊤ : Submodule A A)).mkQ x) =
          (P.ideal • (⊤ : Submodule A B)).mkQ (Algebra.linearMap A B x) :=
    ⟨eQuot, hInd⟩
  have hiso : ∃ e : A ≃ₗ[A] B, e.toLinearMap = Algebra.linearMap A B :=
    finiteProjective_map_isIso_of_inducesQuotientEquiv' (R := A) (M := A) (N := B)
      P.ideal hP (Algebra.linearMap A B) hφ
  obtain ⟨e, he⟩ := hiso
  have he' : Function.Bijective (Algebra.linearMap A B) := by
    rw [← he]
    exact e.bijective
  have hlin : (Algebra.linearMap A B : A → B) = f := by
    exact congrArg (fun g : A →+* B => (g : A → B))
      (RingHom.algebraMap_toAlgebra f)
  rw [← hlin]
  exact he'

/-! ## The finite-helper factorization data -/

/-- Data for the product decomposition used in the finite helper lemma.

The factors are presented as `A ⧸ I`-algebras, so their reductions by the
induced ideal `I` are canonically the factors themselves.  The displayed
condition `A ⧸ I → B₁/IB₁` is therefore represented by surjectivity of the
canonical algebra map to `B₁`. -/
def FiniteHelperFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A)
    (B₁ B₂ : Type w) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]
    (b : B) : Prop :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra (A ⧸ I) (B ⧸ Ideal.map f I) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      (p := I) (P := Ideal.map f I) Ideal.le_comap_map
  ∃ e : (B ⧸ Ideal.map f I) ≃ₐ[A ⧸ I] B₁ × B₂,
    Function.Surjective (algebraMap (A ⧸ I) B₁) ∧
      e (Ideal.Quotient.mk (Ideal.map f I) b) = (1, 0)

/- The étale base extension, product splitting, faithful-flatness descent, and
local-rank arguments in the source are proof steps for the theorem below;
the factorization data records the externally visible product and reduction
hypotheses. -/

/-- For a finite map, a product decomposition modulo a Zariski-pair ideal and
the distinguished element `(1, 0)` produce a monic annihilating polynomial
whose reduction is `(X - 1) X^d` for some positive `d`. -/
theorem helper_finite
    {A B : Type u} [CommRing A] [CommRing B]
    (P : Pair A) (hP : ZariskiPair P)
    (f : A →+* B) (hfinite : RingHom.Finite f)
    (B₁ B₂ : Type w) [CommRing B₁] [CommRing B₂]
    [Algebra (A ⧸ P.ideal) B₁] [Algebra (A ⧸ P.ideal) B₂]
    (b : B) (hfactor : FiniteHelperFactorization f P.ideal B₁ B₂ b) :
    ∃ p : Polynomial A, p.Monic ∧ Polynomial.eval₂ f b p = 0 ∧
      ∃ d : ℕ, 1 ≤ d ∧
        Polynomial.map (Ideal.Quotient.mk P.ideal) p =
          (Polynomial.X - Polynomial.C (1 : A ⧸ P.ideal)) * Polynomial.X ^ d := by
  sorry

/-! ## Jacobson complements -/

/-- In a Noetherian Zariski pair, inverting an element of the distinguished
ideal produces a Jacobson ring. -/
theorem noetherian_zariski_jacobson_complement
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (P : Pair A) (hP : ZariskiPair P) (f : A) (hf : f ∈ P.ideal) :
    IsJacobsonRing (Localization.Away f) := by
  apply Formalization.Books.Algebra.Unit61.noetherian_ring_isJacobson_of_prime_maximal_or_infinite_over
  intro p hp
  by_cases hpmax : p.IsMaximal
  · exact Or.inl hpmax
  right
  let eS := IsLocalization.primeSpectrumOrderIso
    (Submonoid.powers f) (Localization.Away f)
  let pS : PrimeSpectrum (Localization.Away f) := ⟨p, hp⟩
  let qA : Ideal A := (eS pS).1.asIdeal
  have hqA : qA.IsPrime := (eS pS).1.2
  have hqdisj : Disjoint (Submonoid.powers f : Set A) (qA : Set A) :=
    (eS pS).2
  have hqf : f ∉ qA := by
    intro hqf
    exact Set.disjoint_left.mp hqdisj ⟨1, by simp⟩ hqf
  obtain ⟨mS, hmS, hpmS⟩ := Ideal.exists_le_maximal p hp.ne_top
  have hpltS : p < mS := lt_of_le_of_ne hpmS (by
    intro hEq
    exact hpmax (hEq ▸ hmS))
  let q1A : Ideal A := (eS (⟨mS, hmS.isPrime⟩ : PrimeSpectrum _)).1.asIdeal
  have hq1A : q1A.IsPrime := (eS (⟨mS, hmS.isPrime⟩ : PrimeSpectrum _)).1.2
  have hqAq1A : qA ≤ q1A := by
    change (eS pS).1.asIdeal ≤
      (eS (⟨mS, hmS.isPrime⟩ : PrimeSpectrum _)).1.asIdeal
    exact eS.monotone hpmS
  have hqA_lt_q1A : qA < q1A := by
    apply lt_of_le_of_ne hqAq1A
    intro hEq
    apply hpltS.ne
    have h : pS = (⟨mS, hmS.isPrime⟩ : PrimeSpectrum (Localization.Away f)) := by
      apply eS.injective
      apply Subtype.ext
      apply PrimeSpectrum.ext
      exact hEq
    exact congrArg (fun z : PrimeSpectrum (Localization.Away f) => z.asIdeal) h
  have hq1disj : Disjoint (Submonoid.powers f : Set A) (q1A : Set A) :=
    (eS (⟨mS, hmS.isPrime⟩ : PrimeSpectrum _)).2
  have hq1f : f ∉ q1A := by
    intro hq1f
    exact Set.disjoint_left.mp hq1disj ⟨1, by simp⟩ hq1f
  have hq1notmax : ¬ q1A.IsMaximal := by
    intro hq1max
    apply hq1f
    exact (@Ring.jacobson_le_of_isMaximal A _ q1A hq1max) (hP hf)
  let R := A ⧸ qA
  have hdomR : IsDomain R :=
    (Ideal.Quotient.isDomain_iff_prime qA).mpr hqA
  let q1R : PrimeSpectrum R :=
    ⟨Ideal.map (Ideal.Quotient.mk qA) q1A,
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by simpa [Ideal.mk_ker] using hqAq1A)⟩
  have hq1R0 : q1R.asIdeal ≠ (⊥ : Ideal R) := by
    intro hzero
    have hle : q1A ≤ qA := by
      have hker : RingHom.ker (Ideal.Quotient.mk qA) ≥ q1A := by
        have hmap : Ideal.map (Ideal.Quotient.mk qA) q1A = ⊥ := by
          exact hzero
        exact (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk qA)).mp hmap
      simpa [Ideal.mk_ker] using hker
    exact hqA_lt_q1A.ne (le_antisymm hqAq1A hle)
  obtain ⟨mA, hmA, hq1mA⟩ := Ideal.exists_le_maximal q1A hq1A.ne_top
  have hq1ltmA : q1A < mA := lt_of_le_of_ne hq1mA (by
    intro hEq
    exact hq1notmax (hEq ▸ hmA))
  let mR : PrimeSpectrum R :=
    ⟨Ideal.map (Ideal.Quotient.mk qA) mA,
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by simpa [Ideal.mk_ker] using hqAq1A.trans hq1mA)⟩
  have hq1mR : q1R ≤ mR := by
    change Ideal.map (Ideal.Quotient.mk qA) q1A ≤
      Ideal.map (Ideal.Quotient.mk qA) mA
    exact Ideal.map_mono hq1mA
  have hq1ltmR : q1R < mR := by
    apply lt_of_le_of_ne hq1mR
    intro hEq
    have hmap : Ideal.map (Ideal.Quotient.mk qA) q1A =
        Ideal.map (Ideal.Quotient.mk qA) mA := by
      exact congrArg (fun z : PrimeSpectrum R => z.asIdeal) hEq
    have hcomap :
        Ideal.comap (Ideal.Quotient.mk qA)
            (Ideal.map (Ideal.Quotient.mk qA) q1A) =
          Ideal.comap (Ideal.Quotient.mk qA)
            (Ideal.map (Ideal.Quotient.mk qA) mA) := congrArg _ hmap
    have : q1A = mA := by
      simpa only [Ideal.comap_map_mk hqAq1A,
        Ideal.comap_map_mk (hqAq1A.trans hq1mA)] using hcomap
    exact hq1ltmA.ne this
  let : mR.asIdeal.IsPrime := mR.2
  let T := Localization.AtPrime mR.asIdeal
  have hdomT : IsDomain T := by
    exact @IsLocalization.isDomain_of_atPrime R _ hdomR T _ _ mR.asIdeal mR.2 inferInstance
  have hnoethR : IsNoetherianRing R := inferInstance
  have hnoethT : IsNoetherianRing T := by
    exact IsLocalization.isNoetherianRing (M := mR.asIdeal.primeCompl) (S := T) hnoethR
  let eT := IsLocalization.AtPrime.primeSpectrumOrderIso T mR.asIdeal
  let t₀ : PrimeSpectrum T :=
    eT.symm ⟨⟨(⊥ : Ideal R), Ideal.isPrime_bot⟩, by
      change (⊥ : Ideal R) ≤ mR.asIdeal
      exact bot_le⟩
  let t₁ : PrimeSpectrum T := eT.symm ⟨q1R, hq1mR⟩
  let t₂ : PrimeSpectrum T := eT.symm ⟨mR, by
    change mR ≤ (⟨mR.asIdeal, this⟩ : PrimeSpectrum R)
    exact le_rfl⟩
  have ht₀₁ : t₀ < t₁ := by
    apply eT.symm.lt_iff_lt.mpr
    change (⊥ : Ideal R) < q1R.asIdeal
    exact bot_lt_iff_ne_bot.mpr hq1R0
  have ht₁₂ : t₁ < t₂ := by
    apply eT.symm.lt_iff_lt.mpr
    change q1R.asIdeal < mR.asIdeal
    exact hq1ltmR
  let lT : LTSeries (PrimeSpectrum T) :=
    { length := 2
      toFun := fun i => Fin.cases t₀ (fun j => Fin.cases t₁ (fun _ => t₂) j) i
      step := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change t₀ < t₁
          exact ht₀₁
        · have hj : j = 0 := Subsingleton.elim _ _
          subst j
          change t₁ < t₂
          exact ht₁₂ }
  have hdimT : (2 : WithBot ℕ∞) ≤ ringKrullDim T := by
    apply Order.le_krullDim_iff.mpr
    exact ⟨lT, by rfl⟩
  let fR : R := Ideal.Quotient.mk qA f
  let U : Set (PrimeSpectrum T) :=
    PrimeSpectrum.basicOpen (algebraMap R T fR)
  have hUopen : IsOpen U := PrimeSpectrum.isOpen_basicOpen
  have hfq1R : fR ∉ q1R.asIdeal := by
    intro hfq1R
    apply hq1f
    have hmem : f ∈ Ideal.comap (Ideal.Quotient.mk qA)
        (Ideal.map (Ideal.Quotient.mk qA) q1A) := hfq1R
    simpa only [Ideal.comap_map_mk hqAq1A] using hmem
  have hUnonempty : U.Nonempty := by
    refine ⟨t₁, (PrimeSpectrum.mem_basicOpen _ _).mpr ?_⟩
    intro hft₁
    have hunder : fR ∈ t₁.asIdeal.under R := by
      rw [Ideal.mem_under]
      exact hft₁
    change fR ∈ (eT t₁).1.asIdeal at hunder
    exact hfq1R (by simpa [t₁] using hunder)
  have hUinf :=
    @Formalization.Books.Algebra.Unit61.nonempty_open_primeSpectrum_infinite_of_local_noetherian_domain_dim_ge_two
      T _ inferInstance hnoethT hdomT hdimT U hUopen hUnonempty
  let rR : U → Ideal R := fun z => (eT z.1).1.asIdeal
  let rA : U → Ideal A := fun z => Ideal.comap (Ideal.Quotient.mk qA) (rR z)
  have hrRprime (z : U) : (rR z).IsPrime := (eT z.1).1.2
  have hrAprime (z : U) : (rA z).IsPrime := by
    let : (rR z).IsPrime := hrRprime z
    exact Ideal.comap_isPrime _ _
  have hrfR (z : U) : fR ∉ rR z := by
    intro hfr
    have hfr' : fR ∈ (eT z.1).1.asIdeal := by
      simpa [rR] using hfr
    have : algebraMap R T fR ∈ z.1.asIdeal := by
      rw [← Ideal.mem_under]
      exact hfr'
    exact (PrimeSpectrum.mem_basicOpen _ _).mp z.2 this
  have hrfA (z : U) : f ∉ rA z := by
    intro hfr
    apply hrfR z
    change Ideal.Quotient.mk qA f ∈ rR z
    exact hfr
  have hrdisj (z : U) :
      Disjoint (Submonoid.powers f : Set A) (rA z : Set A) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨n, rfl⟩ hx
    exact hrfA z ((hrAprime z).mem_of_pow_mem n hx)
  let rS : U → PrimeSpectrum (Localization.Away f) := fun z =>
    eS.symm ⟨⟨rA z, hrAprime z⟩, hrdisj z⟩
  have hq_rA (z : U) : qA ≤ rA z := by
    change qA ≤ Ideal.comap (Ideal.Quotient.mk qA) (rR z)
    exact (Ideal.mk_ker (I := qA)).symm.le.trans
      (Ideal.ker_le_comap (K := rR z) (Ideal.Quotient.mk qA))
  have hp_rS (z : U) : p ≤ (rS z).asIdeal := by
    have hpr : pS ≤ rS z := by
      apply eS.le_iff_le.mp
      change (eS pS).1.asIdeal ≤ (eS (rS z)).1.asIdeal
      simpa [rS] using hq_rA z
    exact hpr
  let F : U → {q : Ideal (Localization.Away f) // q.IsPrime ∧ p ≤ q} := fun z =>
    ⟨(rS z).asIdeal, (rS z).2, hp_rS z⟩
  have hFinj : Function.Injective F := by
    intro z z' hzz'
    have hS : rS z = rS z' := by
      have hSas : (rS z).asIdeal = (rS z').asIdeal :=
        congrArg
          (fun q : {q : Ideal (Localization.Away f) // q.IsPrime ∧ p ≤ q} => q.1)
          hzz'
      exact PrimeSpectrum.ext hSas
    have hA : rA z = rA z' := by
      have h := congrArg (fun x => (eS x).1.asIdeal) hS
      simpa [rS] using h
    have hR : rR z = rR z' := by
      apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk qA)
        Ideal.Quotient.mk_surjective
      simpa [rA] using hA
    have hT : eT z.1 = eT z'.1 := by
      apply Subtype.ext
      apply PrimeSpectrum.ext
      exact hR
    exact Subtype.ext (eT.injective hT)
  let : Infinite U := Set.infinite_coe_iff.mpr hUinf
  have htarget : Infinite {q : Ideal (Localization.Away f) // q.IsPrime ∧ p ≤ q} :=
    Infinite.of_injective F hFinj
  exact Set.infinite_coe_iff.mp htarget

end

end Formalization.Books.MoreAlgebra.Unit10
