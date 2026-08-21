import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit78.FiniteProjectiveModules
import Formalization.Books.Algebra.Unit112.HomomorphismsAndDimension
import Formalization.Books.Algebra.Unit113.DimensionFormula
import Formalization.Books.Algebra.Unit135.LocalCompleteIntersections
import Formalization.Books.Algebra.Unit126.AlgebrasAndModulesFinitePresentation
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.Extension.Cotangent.Basis

/-!
# Commutative Algebra, Chapter 136: Syntomic morphisms

This file follows the source order of the section.  The local-complete-
intersection condition on a fibre reuses
`Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection`; ring maps,
base change, localization, conormal modules, and finite projectivity likewise
use the canonical Mathlib and earlier-chapter interfaces.
-/

namespace Formalization.Books.Algebra.Unit136

open Set
open Module
open scoped BigOperators TensorProduct

noncomputable section

universe u v

/-! ## Syntomic maps and their first permanence properties -/

/-- The affine fibre of `R → S` over `p : Spec R`. -/
abbrev Fiber (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : PrimeSpectrum R) : Type _ :=
  p.asIdeal.Fiber S

/-- A syntomic ring map: flat, finitely presented, with lci fibres. -/
def IsSyntomic
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  RingHom.Flat f ∧ RingHom.FinitePresentation f ∧
    ∀ p : PrimeSpectrum R,
      letI : Algebra p.asIdeal.ResidueField (Fiber R S p) :=
        Algebra.TensorProduct.leftAlgebra
      Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection
        p.asIdeal.ResidueField (Fiber R S p)

theorem IsSyntomic.flat
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (h : IsSyntomic f) : RingHom.Flat f := by
  simpa only [IsSyntomic] using h.1

theorem IsSyntomic.finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (h : IsSyntomic f) : RingHom.FinitePresentation f := by
  simpa only [IsSyntomic] using h.2.1

theorem IsSyntomic.fiber_lci
    {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (h : IsSyntomic f) (p : PrimeSpectrum R) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra p.asIdeal.ResidueField (Fiber R S p) :=
      Algebra.TensorProduct.leftAlgebra
    Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection
      p.asIdeal.ResidueField (Fiber R S p) := by
  simpa only [IsSyntomic] using h.2.2 p

private theorem isGlobalCompleteIntersection_of_algEquiv
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : Formalization.Books.Algebra.Unit135.IsGlobalCompleteIntersection k A) :
    Formalization.Books.Algebra.Unit135.IsGlobalCompleteIntersection k B := by
  rcases hA with ⟨hft, hcase⟩
  rcases hcase with hsub | ⟨n, c, P, f, hker, hc, hdim⟩
  · let hsubB : Subsingleton B :=
      ⟨fun x y => e.symm.injective (hsub.elim _ _)⟩
    let Q : Formalization.Books.Algebra.Unit135.PolynomialPresentation k B 0 :=
      Algebra.Generators.ofSurjective
        (fun i : Fin 0 => nomatch i)
        (by
          intro x
          exact ⟨0, hsubB.elim _ _⟩)
    exact ⟨RingHom.finiteType_algebraMap.mpr Q.finiteType, Or.inl hsubB⟩
  · let P' : Formalization.Books.Algebra.Unit135.PolynomialPresentation k B n :=
      P.ofAlgEquiv e
    have hker' : P'.ker = P.ker := by
      rw [P'.ker_eq_ker_aeval_val, P.ker_eq_ker_aeval_val]
      ext z
      change MvPolynomial.aeval (e ∘ P.val) z = 0 ↔
        MvPolynomial.aeval P.val z = 0
      have heval : e (MvPolynomial.aeval P.val z) =
          MvPolynomial.aeval (e ∘ P.val) z := by
        simpa [Function.comp_def] using
          (MvPolynomial.comp_aeval_apply (R := k) (f := P.val) e.toAlgHom z)
      rw [← heval]
      constructor
      · intro hz
        apply e.injective
        simpa using hz
      · intro hz
        rw [← e.map_zero]
        exact congrArg e hz
    have hdim' : ringKrullDim B =
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      exact hdim
    exact ⟨RingHom.finiteType_algebraMap.mpr P'.finiteType, Or.inr
      ⟨n, c, P', f, hker'.trans hker, hc, hdim'⟩⟩

private theorem local_complete_intersection_of_algEquiv
    {k A B : Type u} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B)
    (hA : Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k A) :
    Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k B := by
  rcases hA with ⟨hft, n, gs, hopen, hglob⟩
  have hftB : RingHom.FiniteType (algebraMap k B) := by
    rw [RingHom.finiteType_algebraMap]
    exact Algebra.FiniteType.equiv (by
      rw [RingHom.finiteType_algebraMap] at hft
      exact hft) e
  refine ⟨hftB, n, (fun i => e (gs i)), ?_, ?_⟩
  · ext q
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    let qA : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
    have hq : qA ∈ ⋃ i : Fin n,
        (PrimeSpectrum.basicOpen (gs i) : Set (PrimeSpectrum A)) := by
      rw [hopen]
      trivial
    rcases Set.mem_iUnion.mp hq with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change e (gs i) ∉ q.asIdeal
    change gs i ∉ qA.asIdeal
    exact hi
  · intro i
    have hmap : Submonoid.map e.toRingEquiv (Submonoid.powers (gs i)) =
        Submonoid.powers (e (gs i)) := by
      ext x
      constructor
      · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, by simp⟩
      · rintro ⟨m, rfl⟩
        exact ⟨(gs i) ^ m, ⟨m, rfl⟩, by simp⟩
    let ei : Localization.Away (gs i) ≃ₐ[k]
        Localization.Away (e (gs i)) :=
      IsLocalization.algEquivOfAlgEquiv
        (Localization.Away (gs i)) (Localization.Away (e (gs i))) e hmap
    exact isGlobalCompleteIntersection_of_algEquiv ei (hglob i)

private noncomputable def fiber_base_change_algEquiv
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (p : PrimeSpectrum R)
    (p' : PrimeSpectrum R') (hp' : PrimeSpectrum.comap g p' = p) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    let K := p'.asIdeal.ResidueField
    let k₀ := p.asIdeal.ResidueField
    letI : Algebra k₀ K :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' hp').toAlgebra
    letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
    K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[k₀] (k₀ ⊗[R] S) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let K := p'.asIdeal.ResidueField
  let k₀ := p.asIdeal.ResidueField
  letI : Algebra k₀ K :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' hp').toAlgebra
  letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  letI : IsScalarTower R k₀ K := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    have hideal : p.asIdeal = p'.asIdeal.comap g := by
      simpa [PrimeSpectrum.comap_asIdeal] using
        (congrArg PrimeSpectrum.asIdeal hp').symm
    change algebraMap R K r =
      (Ideal.ResidueField.map p.asIdeal p'.asIdeal g hideal)
        (algebraMap R k₀ r)
    rw [Ideal.ResidueField.map_algebraMap]
    exact (IsScalarTower.algebraMap_apply R R' K r).symm
  let e₀ : K ⊗[R'] (R' ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R R' K K S
  let e₁ : K ⊗[k₀] (k₀ ⊗[R] S) ≃ₐ[K] K ⊗[R] S :=
    Algebra.TensorProduct.cancelBaseChange R k₀ K K S
  let c : K ⊗[R'] (S ⊗[R] R') ≃ₐ[K] K ⊗[R'] (R' ⊗[R] S) :=
    Algebra.TensorProduct.congr (.refl : K ≃ₐ[K] K)
      (Algebra.TensorProduct.commRight R R' S).symm
  exact c.trans e₀ |>.trans e₁.symm

private noncomputable def fiber_localization_algEquiv
    {R S k : Type u} [CommRing R] [CommRing S] [Field k]
    [Algebra R S] [Algebra R k] (g₀ : S) :
    let U := Localization.Away g₀
    let F := k ⊗[R] S
    letI : Algebra R U :=
      ((algebraMap S U).comp (algebraMap R S)).toAlgebra
    letI : Module R U := Algebra.toModule
    letI : SMul S U := Algebra.toSMul
    letI : SMul R U := Algebra.toSMul
    letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
    k ⊗[R] U ≃ₐ[k] Localization.Away (algebraMap S F g₀) := by
  dsimp
  let U := Localization.Away g₀
  let F := k ⊗[R] S
  letI : Algebra R U :=
    ((algebraMap S U).comp (algebraMap R S)).toAlgebra
  letI : Module R U := Algebra.toModule
  letI : SMul S U := Algebra.toSMul
  letI : SMul R U := Algebra.toSMul
  letI : IsScalarTower R S U := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    simp [RingHom.algebraMap_toAlgebra]
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  let c₁ : S ⊗[R] k ≃ₐ[S] F :=
    Algebra.TensorProduct.commRight R S k
  let c₂ : U ⊗[S] (S ⊗[R] k) ≃ₐ[U] U ⊗[S] F :=
    Algebra.TensorProduct.congr (.refl : U ≃ₐ[U] U) c₁
  letI : Algebra U (U ⊗[R] k) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra U (k ⊗[R] U) := Algebra.TensorProduct.rightAlgebra
  let c₃ : U ⊗[S] (S ⊗[R] k) ≃ₐ[U] U ⊗[R] k :=
    Algebra.TensorProduct.cancelBaseChange R S U U k
  let c₄ : U ⊗[R] k ≃ₐ[U] k ⊗[R] U :=
    Algebra.TensorProduct.commRight R U k
  let c : U ⊗[S] F ≃ₐ[U] k ⊗[R] U := c₂.symm.trans c₃ |>.trans c₄
  letI : Algebra F (U ⊗[S] F) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra k (U ⊗[S] F) :=
    Algebra.restrictScalars k F (U ⊗[S] F)
  letI : IsScalarTower k F (U ⊗[S] F) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  let e₀ : k ⊗[R] U ≃ₐ[k] U ⊗[S] F :=
    { c.symm.toRingEquiv with
      commutes' := by
        intro x
        change c.symm (algebraMap k (k ⊗[R] U) x) =
          algebraMap k (U ⊗[S] F) x
        change c.symm (x ⊗ₜ[R] (1 : U)) =
          (1 : U) ⊗ₜ[S] (x ⊗ₜ[R] (1 : S))
        simp [c, c₂, c₃, c₄]
        rw [Algebra.TensorProduct.commRight_tmul] }
  let e₁ : U ⊗[S] F ≃ₐ[k] Localization.Away (algebraMap S F g₀) :=
    (IsLocalization.Away.tensorRightEquiv (r := g₀) F U).restrictScalars k
  exact e₀.trans e₁

theorem syntomic_over_field_iff_local_complete_intersection
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] :
    IsSyntomic (algebraMap k S) ↔
      Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S := by
  constructor
  · intro h
    let alg₀ : Algebra k S := inferInstance
    letI : Algebra k S := (algebraMap k S).toAlgebra
    have hft : RingHom.FiniteType (algebraMap k S) :=
      RingHom.FiniteType.of_finitePresentation h.finitePresentation
    rw [RingHom.finiteType_algebraMap] at hft
    let _ : Algebra.FiniteType k S := hft
    let p : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : Field p.asIdeal.ResidueField := inferInstance
    have hp := h.fiber_lci p
    have he :=
      Formalization.Books.Algebra.Unit135.local_complete_intersection_field_change
        (k := k) (K := p.asIdeal.ResidueField) (S := S)
    have hlci : Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S := by
      apply he.mpr
      convert hp using 1
    have halg : (algebraMap k S).toAlgebra = alg₀ :=
      by
        exact @toAlgebra_algebraMap k S _ _ alg₀
    have hprop :
        @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _
            (algebraMap k S).toAlgebra =
          @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _ alg₀ :=
      congrArg (fun a : Algebra k S =>
        @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _ a) halg
    change @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _ alg₀
    exact hprop ▸ hlci
  · intro h
    let alg₀ : Algebra k S := inferInstance
    letI : Algebra k S := (algebraMap k S).toAlgebra
    have halg : (algebraMap k S).toAlgebra = alg₀ :=
      by
        exact @toAlgebra_algebraMap k S _ _ alg₀
    have hprop :
        @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _
            (algebraMap k S).toAlgebra =
          @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _ alg₀ :=
      congrArg (fun a : Algebra k S =>
        @Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S _ _ a) halg
    have hlocal : Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k S :=
      hprop.symm ▸ h
    have hft : RingHom.FiniteType (algebraMap k S) := hlocal.finiteType
    have hfp : RingHom.FinitePresentation (algebraMap k S) :=
      (RingHom.FinitePresentation.of_finiteType).mp hft
    rw [RingHom.finiteType_algebraMap] at hft
    let _ : Algebra.FiniteType k S := hft
    refine ⟨?_, hfp, ?_⟩
    · change Module.Flat k S
      infer_instance
    · intro p
      letI : p.asIdeal.IsPrime := p.isPrime
      letI : Field p.asIdeal.ResidueField := inferInstance
      letI : Module k p.asIdeal.ResidueField :=
        IsLocalRing.instModuleResidueFieldOfAlgebra (Localization.AtPrime p.asIdeal)
      have he :=
        Formalization.Books.Algebra.Unit135.local_complete_intersection_field_change
          (k := k) (K := p.asIdeal.ResidueField) (S := S)
      have hp' := he.mp hlocal
      convert hp' using 1

private theorem syntomic_base_change_core
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : IsSyntomic f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsSyntomic (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let f' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
  letI : Algebra R' (S ⊗[R] R') := f'.toAlgebra
  have hflat : RingHom.Flat f' := by
    change Module.Flat R' (S ⊗[R] R')
    letI : Module.Flat R S := hf.flat
    letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
    letI : Module.Flat R' (R' ⊗[R] S) := inferInstance
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' S).symm.toLinearEquiv
  have hfp : RingHom.FinitePresentation f' :=
    Formalization.Books.Algebra.Unit14.baseChange_finite_presentation
      f g hf.finitePresentation
  refine ⟨hflat, hfp, ?_⟩
  intro p'
  let p : PrimeSpectrum R := PrimeSpectrum.comap g p'
  let K := p'.asIdeal.ResidueField
  let k₀ := p.asIdeal.ResidueField
  letI : Algebra k₀ K :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' rfl).toAlgebra
  let e := fiber_base_change_algEquiv f g p p' rfl
  letI : Algebra.FiniteType R S := by
    change RingHom.FiniteType f
    exact RingHom.FiniteType.of_finitePresentation hf.finitePresentation
  letI : Algebra.FiniteType k₀ (k₀ ⊗[R] S) := by infer_instance
  have hfield :
      Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k₀
          (k₀ ⊗[R] S) ↔
        Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection K
          (K ⊗[k₀] (k₀ ⊗[R] S)) :=
    Formalization.Books.Algebra.Unit135.local_complete_intersection_field_change
      (k := k₀) (K := K) (S := k₀ ⊗[R] S)
  exact local_complete_intersection_of_algEquiv e.symm
    (hfield.mp (hf.fiber_lci p))

theorem syntomic_descends
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hff : RingHom.FaithfullyFlat g) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsSyntomic f ↔
      IsSyntomic (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let f' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
  letI : Algebra R' (S ⊗[R] R') := f'.toAlgebra
  constructor
  · intro hf
    exact syntomic_base_change_core f g hf
  · intro hb
    have hflat : RingHom.Flat f := by
      change Module.Flat R S
      letI : Module.FaithfullyFlat R R' := hff
      letI : Algebra R' (S ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
      have hmap : algebraMap R' (S ⊗[R] R') = f' := by
        ext r
        rfl
      have hbflat : Module.Flat R' (S ⊗[R] R') := by
        rw [← RingHom.flat_algebraMap_iff, hmap]
        exact hb.flat
      letI : Module.Flat R' (S ⊗[R] R') := hbflat
      letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
      letI : Module.Flat R' (R' ⊗[R] S) :=
        Module.Flat.of_linearEquiv
          (Algebra.TensorProduct.commRight R R' S).toLinearEquiv
      exact Module.Flat.of_flat_tensorProduct (R := R) (M := S) R'
    have hfp : RingHom.FinitePresentation f :=
      (Formalization.Books.Algebra.Unit126.finite_presentation_descends f g hff).mpr
        hb.finitePresentation
    refine ⟨hflat, hfp, ?_⟩
    intro p
    letI : Module.FaithfullyFlat R R' := hff
    have hsurj : Function.Surjective (PrimeSpectrum.comap g) :=
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2
    obtain ⟨p', hp'⟩ := hsurj p
    let K := p'.asIdeal.ResidueField
    let k₀ := p.asIdeal.ResidueField
    letI : Algebra k₀ K :=
      (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' hp').toAlgebra
    let e := fiber_base_change_algEquiv f g p p' hp'
    letI : Algebra.FiniteType R S := by
      change RingHom.FiniteType f
      exact RingHom.FiniteType.of_finitePresentation hfp
    letI : Algebra.FiniteType k₀ (k₀ ⊗[R] S) := by infer_instance
    have hfield :
        Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection k₀
            (k₀ ⊗[R] S) ↔
          Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection K
            (K ⊗[k₀] (k₀ ⊗[R] S)) :=
      Formalization.Books.Algebra.Unit135.local_complete_intersection_field_change
        (k := k₀) (K := K) (S := k₀ ⊗[R] S)
    exact hfield.mpr (local_complete_intersection_of_algEquiv e
      (hb.fiber_lci p'))

theorem syntomic_base_change
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (hf : IsSyntomic f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsSyntomic (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  exact syntomic_base_change_core f g hf

theorem syntomic_local_on_source
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (m : ℕ) (gs : Fin m → S)
    (hgen : Ideal.span (Set.range gs) = (⊤ : Ideal S)) :
    letI : Algebra R S := f.toAlgebra
    (∀ i, IsSyntomic (algebraMap R (Localization.Away (gs i)))) →
      IsSyntomic f := by
  letI : Algebra R S := f.toAlgebra
  intro hlocal
  have hflat : RingHom.Flat f :=
    RingHom.Flat.propertyIsLocal.ofLocalizationSpanTarget f (Set.range gs) hgen
      (by
        rintro ⟨r, ⟨i, rfl⟩⟩
        have hmap :
            (algebraMap S (Localization.Away (gs i))).comp f =
              algebraMap R (Localization.Away (gs i)) := by
          ext r
          simpa [RingHom.algebraMap_toAlgebra] using
            (IsScalarTower.algebraMap_apply R S (Localization.Away (gs i)) r).symm
        rw [hmap]
        exact (hlocal i).flat)
  have hfp : RingHom.FinitePresentation f :=
    RingHom.finitePresentation_isLocal.ofLocalizationSpanTarget f (Set.range gs) hgen
      (by
        rintro ⟨r, ⟨i, rfl⟩⟩
        have hmap :
            (algebraMap S (Localization.Away (gs i))).comp f =
              algebraMap R (Localization.Away (gs i)) := by
          ext r
          simpa [RingHom.algebraMap_toAlgebra] using
            (IsScalarTower.algebraMap_apply R S (Localization.Away (gs i)) r).symm
        rw [hmap]
        exact (hlocal i).finitePresentation)
  refine ⟨hflat, hfp, ?_⟩
  intro p
  let F := Fiber R S p
  let k₀ := p.asIdeal.ResidueField
  letI : Algebra k₀ F := Algebra.TensorProduct.leftAlgebra
  letI : Algebra S F := Algebra.TensorProduct.rightAlgebra
  have hgenF : Ideal.span (Set.range (fun i => algebraMap S F (gs i))) = (⊤ : Ideal F) := by
    calc
      Ideal.span (Set.range (fun i => algebraMap S F (gs i))) =
          Ideal.map (algebraMap S F) (Ideal.span (Set.range gs)) := by
            rw [Ideal.map_span]
            congr 1
            ext x
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨gs i, ⟨i, rfl⟩, rfl⟩
            · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
              exact ⟨i, rfl⟩
      _ = Ideal.map (algebraMap S F) (⊤ : Ideal S) := by rw [hgen]
      _ = ⊤ := Ideal.map_top (algebraMap S F)
  have hlocF : ∀ i, Formalization.Books.Algebra.Unit135.IsLocalCompleteIntersection
      k₀ (Localization.Away (algebraMap S F (gs i))) := by
    intro i
    let e := fiber_localization_algEquiv (R := R) (S := S) (k := k₀) (gs i)
    exact local_complete_intersection_of_algEquiv e
      (by simpa [Fiber, F, k₀] using (hlocal i).fiber_lci p)
  exact Formalization.Books.Algebra.Unit135.local_complete_intersection_of_localizationSpanTarget
    m (fun i => algebraMap S F (gs i)) hgenF hlocF

/-! ## Relative global complete intersections -/

/-- A finite polynomial presentation with named relations. -/
def IsPolynomialQuotientPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring) : Prop :=
  P.ker = Ideal.ofList (List.ofFn fs)

/-- A relative global complete intersection presentation over a ring. -/
def IsRelativeGlobalCompleteIntersection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
    ∃ (n c : ℕ) (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n)) (fs : Fin c → P.Ring),
    IsPolynomialQuotientPresentation P fs ∧
      ∀ p : PrimeSpectrum R,
        Nonempty (PrimeSpectrum (Fiber R S p)) →
          c ≤ n ∧
          ringKrullDim (Fiber R S p) =
            (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)

/-- Every nonempty fibre of a ring map has the displayed dimension. -/
def HasFiberDimension
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (d : WithBot ℕ∞) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∀ p : PrimeSpectrum R,
    Nonempty (PrimeSpectrum (Fiber R S p)) →
      ringKrullDim (Fiber R S p) = d

/-- The image of an element of `S` in the canonical fibre over `p`. -/
def IsUnitInFiber
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (g : S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  IsUnit ((Algebra.TensorProduct.includeRight :
    S →ₐ[R] Fiber R S p) g)

/-- The dimension of the local fibre at a prime of `S` over a prime of `R`. -/
def LocalFiberDimensionAt
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) : WithBot ℕ∞ :=
  letI : Algebra R S := f.toAlgebra
  ringKrullDim
    (Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying)

theorem relative_global_complete_intersection_is_finite_presentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : IsRelativeGlobalCompleteIntersection f) :
    RingHom.FinitePresentation f := by
  letI : Algebra R S := f.toAlgebra
  rcases h with ⟨n, c, P, fs, hP, _⟩
  have hker : P.ker.FG := by
    rw [hP]
    change Submodule.FG (Ideal.ofList (List.ofFn fs))
    rw [Ideal.ofList]
    rw [← show Set.range fs = {x | x ∈ List.ofFn fs} by
      ext x
      simp]
    exact Submodule.fg_span (R := P.Ring) (M := P.Ring) (Set.finite_range fs)
  have hPfp : RingHom.FinitePresentation (algebraMap P.Ring S) :=
    RingHom.FinitePresentation.of_surjective (algebraMap P.Ring S)
      P.algebraMap_surjective hker
  have hpoly : RingHom.FinitePresentation (algebraMap R P.Ring) := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hcomp := hPfp.comp hpoly
  have hmap : (algebraMap P.Ring S).comp (algebraMap R P.Ring) = f := by
    ext r
    simp [P.algebraMap_eq, RingHom.algebraMap_toAlgebra]
  rw [hmap] at hcomp
  exact hcomp

theorem relative_global_complete_intersection_base_change
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R') (h : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    IsRelativeGlobalCompleteIntersection
      (Formalization.Books.Algebra.Unit14.baseChangeRingMap f g) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R R' := g.toAlgebra
  let f' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
  letI : Algebra R' (S ⊗[R] R') := f'.toAlgebra
  rcases h with ⟨n, c, P, fs, hP, hdim⟩
  let P₀ : Algebra.Presentation R S (Fin n) (Fin c) :=
    { __ := P
      relation := fs
      span_range_relation_eq_ker := by
        rw [hP]
        change Ideal.span (Set.range fs) =
          Ideal.span {x | x ∈ List.ofFn fs}
        congr 1
        ext x
        simp }
  let P₁ := P₀.baseChange R'
  let P₂ := P₁.ofAlgEquiv (Algebra.TensorProduct.commRight R R' S)
  let P' : Formalization.Books.Algebra.Unit134.Presentation R'
      (S ⊗[R] R') (Fin n) := P₂.toGenerators
  let fs' : Fin c → P'.Ring := fun i => P₂.relation i
  have hP' : IsPolynomialQuotientPresentation P' fs' := by
    change P₂.ker = Ideal.ofList (List.ofFn fs')
    rw [← P₂.span_range_relation_eq_ker]
    change Ideal.span (Set.range P₂.relation) =
      Ideal.ofList (List.ofFn fs')
    rw [Ideal.ofList]
    congr 1
    ext x
    simp [fs']
  refine ⟨n, c, P', fs', hP', ?_⟩
  intro p' hnon
  let p : PrimeSpectrum R := PrimeSpectrum.comap g p'
  let K := p'.asIdeal.ResidueField
  let k₀ := p.asIdeal.ResidueField
  letI : Algebra k₀ K :=
    (Formalization.Books.Algebra.Unit113.residueFieldMapAt g p p' rfl).toAlgebra
  letI : Algebra.FiniteType R S := P.finiteType
  letI : Algebra.FiniteType k₀ (k₀ ⊗[R] S) := by infer_instance
  let e := fiber_base_change_algEquiv f g p p' rfl
  let q' : PrimeSpectrum (Fiber R' (S ⊗[R] R') p') := Classical.choice hnon
  let qK : PrimeSpectrum (K ⊗[k₀] (k₀ ⊗[R] S)) :=
    PrimeSpectrum.comap e.symm.toRingHom q'
  let q : PrimeSpectrum (Fiber R S p) :=
    PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom qK
  have hnonold : Nonempty (PrimeSpectrum (Fiber R S p)) := ⟨q⟩
  have hdimext : ringKrullDim (Fiber R S p) =
      ringKrullDim (K ⊗[k₀] (k₀ ⊗[R] S)) :=
    Formalization.Books.Algebra.Unit116.dimension_preserved_field_extension
      (k := k₀) (S := k₀ ⊗[R] S) (K := K)
  refine ⟨?_, ?_⟩
  · exact (hdim p hnonold).1
  · calc
      ringKrullDim (Fiber R' (S ⊗[R] R') p') =
          ringKrullDim (K ⊗[k₀] (k₀ ⊗[R] S)) :=
        ringKrullDim_eq_of_ringEquiv e.toRingEquiv
      _ = ringKrullDim (Fiber R S p) := hdimext.symm
      _ = (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) := hdim p hnonold |>.2

theorem relative_global_complete_intersection_localization
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    :
    letI : Algebra R S := f.toAlgebra
      ∀ (g₀ : S) (n : ℕ)
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (c : ℕ) (fs : Fin c → P.Ring) (hc : c ≤ n),
      IsPolynomialQuotientPresentation P fs →
      HasFiberDimension f
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) →
      ∀ (h₀ : P.Ring), algebraMap P.Ring S h₀ = g₀ →
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g₀)) := by
  sorry

private theorem relative_global_complete_intersection_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (fA : R →+* A) (fB : R →+* B) (e : A ≃+* B)
    (he : e.toRingHom.comp fA = fB)
    (h : IsRelativeGlobalCompleteIntersection fA) :
    IsRelativeGlobalCompleteIntersection fB := by
  letI : Algebra R A := fA.toAlgebra
  letI : Algebra R B := fB.toAlgebra
  let e' : A ≃ₐ[R] B :=
    { toRingEquiv := e
      commutes' := by
        intro r
        exact congrArg (fun z => z r) he }
  rcases h with ⟨n, c, P, fs, hP, hdim⟩
  let P' := P.ofAlgEquiv e'
  have hker : P'.ker = P.ker := by
    rw [P'.ker_eq_ker_aeval_val, P.ker_eq_ker_aeval_val]
    ext z
    change MvPolynomial.aeval (e' ∘ P.val) z = 0 ↔
      MvPolynomial.aeval P.val z = 0
    have heval : e' (MvPolynomial.aeval P.val z) =
        MvPolynomial.aeval (e' ∘ P.val) z := by
      simpa [Function.comp_def] using
        (MvPolynomial.comp_aeval_apply (R := R) (f := P.val) e'.toAlgHom z)
    rw [← heval]
    constructor
    · intro hz
      apply e'.injective
      simpa using hz
    · intro hz
      rw [← e'.map_zero]
      exact congrArg e' hz
  have hP' : IsPolynomialQuotientPresentation P' fs := by
    exact hker.trans hP
  refine ⟨n, c, P', fs, hP', ?_⟩
  intro p hnon
  let k := p.asIdeal.ResidueField
  let ef : Fiber R A p ≃ₐ[k] Fiber R B p :=
    Algebra.TensorProduct.congr (.refl : k ≃ₐ[k] k) e'
  let qB : PrimeSpectrum (Fiber R B p) := Classical.choice hnon
  let qA : PrimeSpectrum (Fiber R A p) :=
    PrimeSpectrum.comap ef.toRingHom qB
  have hdimA := hdim p (show Nonempty (PrimeSpectrum (Fiber R A p)) from ⟨qA⟩)
  refine ⟨hdimA.1, ?_⟩
  calc
    ringKrullDim (Fiber R B p) = ringKrullDim (Fiber R A p) :=
      (ringKrullDim_eq_of_ringEquiv ef.toRingEquiv).symm
    _ = (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) := hdimA.2

theorem relative_global_complete_intersection_localization_of_base
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (r : R) (g : Localization.Away r →+* S)
    (hfactor : g.comp (algebraMap R (Localization.Away r)) = f)
    (h : IsRelativeGlobalCompleteIntersection f) :
    IsRelativeGlobalCompleteIntersection g := by
  letI : Algebra R S := f.toAlgebra
  let f' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f
    (algebraMap R (Localization.Away r))
  have hbase := relative_global_complete_intersection_base_change f
    (algebraMap R (Localization.Away r)) h
  have hunit : IsUnit (algebraMap R S r) := by
    have hunit' : IsUnit (g (algebraMap R (Localization.Away r) r)) :=
      (IsLocalization.Away.algebraMap_isUnit r).map g
    have heq : g (algebraMap R (Localization.Away r) r) = f r :=
      congrArg (fun k : Localization.Away r →+* S =>
        k (algebraMap R (Localization.Away r) r)) hfactor
    rw [show algebraMap R S r = g (algebraMap R (Localization.Away r) r) by
      simpa [RingHom.algebraMap_toAlgebra] using heq.symm]
    exact hunit'
  letI : IsLocalization.Away (algebraMap R S r) S :=
    IsLocalization.away_of_isUnit_of_bijective S hunit
      Function.bijective_id
  let eS : S ⊗[R] Localization.Away r ≃ₐ[S] S := by
    exact (IsLocalization.Away.tensorEquiv (R := R) (S := S) (r := r) S).trans
      (IsLocalization.atUnit S (algebraMap R S r) hunit).symm
  have he : eS.toRingHom.comp f' = g := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers r)
    intro x
    simp [eS, f', Formalization.Books.Algebra.Unit14.baseChangeRingMap,
      IsLocalization.Away.tensorEquiv]
  exact relative_global_complete_intersection_of_algEquiv f' g
    eS.toRingEquiv he hbase

/-! ## Huber's presentation lemma -/

/-- The conormal module of a finite polynomial presentation is free. -/
def HasFreeConormalPresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ (n : ℕ)
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n)),
    Module.Free S P.toExtension.Cotangent

/-- The classes of named relations form the indicated conormal basis. -/
def HasConormalBasisPresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ}
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
    (fs : Fin c → P.Ring) : Prop :=
  ∃ hmem : ∀ i, fs i ∈ P.toExtension.ker,
    ∃ b : Basis (Fin c) S P.toExtension.Cotangent,
      ∀ i, b i = Algebra.Extension.Cotangent.mk ⟨fs i, hmem i⟩

theorem huber_presentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hfp : RingHom.FinitePresentation f)
    (hconormal : HasFreeConormalPresentation f) :
    letI : Algebra R S := f.toAlgebra
    ∃ (m c : ℕ)
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin m))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs ∧
        HasConormalBasisPresentation P fs := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.FinitePresentation R S := hfp
  rcases hconormal with ⟨n, P, hfree⟩
  letI : Module.Free S P.toExtension.Cotangent := hfree
  obtain ⟨P₁, b, hval, hb⟩ :=
    Algebra.Generators.exists_presentation_of_free_cotangent P
  let evar : Fin (1 + n) ≃ Unit ⊕ Fin n :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl (Fin n)))
  let r := Module.finrank S P.toExtension.Cotangent
  let erel : Fin (1 + r) ≃ Unit ⊕ Fin r :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl (Fin r)))
  let P₂ := P₁.reindex evar erel
  let H : P₁.toGenerators.Hom P₂.toGenerators :=
    { val := fun i => MvPolynomial.X (evar.symm i)
      aeval_val := by
        intro i
        simp [P₂, evar, Algebra.Generators.reindex_val] }
  let H' : P₂.toGenerators.Hom P₁.toGenerators :=
    { val := fun i => MvPolynomial.X (evar i)
      aeval_val := by
        intro i
        simp [P₂, evar, Algebra.Generators.reindex_val] }
  have hHH : H'.toExtensionHom.comp H.toExtensionHom =
      Algebra.Extension.Hom.id _ := by
    rw [← Algebra.Generators.Hom.toExtensionHom_comp]
    have hgen : H'.comp H = Algebra.Generators.Hom.id _ := by
      apply Algebra.Generators.Hom.ext
      exact funext (fun i => by
        rcases i with a | b <;> simp [H, H', evar])
    rw [hgen, Algebra.Generators.Hom.toExtensionHom_id]
  have hH'H : H.toExtensionHom.comp H'.toExtensionHom =
      Algebra.Extension.Hom.id _ := by
    rw [← Algebra.Generators.Hom.toExtensionHom_comp]
    have hgen : H.comp H' = Algebra.Generators.Hom.id _ := by
      apply Algebra.Generators.Hom.ext
      exact funext (fun i => by
        rcases i with a | b <;> simp [H, H', evar])
    rw [hgen, Algebra.Generators.Hom.toExtensionHom_id]
  let E : P₁.toExtension.Cotangent ≃ₗ[S] P₂.toExtension.Cotangent :=
    LinearEquiv.ofLinear
      (Algebra.Extension.Cotangent.map H.toExtensionHom)
      (Algebra.Extension.Cotangent.map H'.toExtensionHom) (by
        calc
          _ = Algebra.Extension.Cotangent.map
              (H.toExtensionHom.comp H'.toExtensionHom) := by
            simpa using
              (Algebra.Extension.Cotangent.map_comp (P'' := P₂.toExtension)
                H'.toExtensionHom H.toExtensionHom).symm
          _ = _ := by rw [hH'H, Algebra.Extension.Cotangent.map_id]) (by
        calc
          _ = Algebra.Extension.Cotangent.map
              (H'.toExtensionHom.comp H.toExtensionHom) := by
            simpa using
              (Algebra.Extension.Cotangent.map_comp (P'' := P₁.toExtension)
                H.toExtensionHom H'.toExtensionHom).symm
          _ = _ := by rw [hHH, Algebra.Extension.Cotangent.map_id])
  let b₂ : Module.Basis (Unit ⊕ Fin r) S P₂.toExtension.Cotangent := b.map E
  let b₃ : Module.Basis (Fin (1 + r)) S P₂.toExtension.Cotangent :=
    b₂.reindex erel.symm
  let P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin (1 + n)) :=
    P₂.toGenerators
  let fs : Fin (1 + r) → P.Ring := fun i => P₂.relation i
  refine ⟨1 + n, 1 + r, P, fs, ?_, ?_⟩
  · change P₂.ker = Ideal.ofList (List.ofFn fs)
    rw [← P₂.span_range_relation_eq_ker]
    change Ideal.span (Set.range P₂.relation) = Ideal.ofList (List.ofFn fs)
    rw [Ideal.ofList]
    congr 1
    ext x
    simp [fs]
  · refine ⟨?_, b₃, ?_⟩
    · intro i
      change P₂.relation i ∈ P₂.ker
      exact P₂.relation_mem_ker i
    intro i
    simp only [b₃, Module.Basis.reindex_apply, b₂, Module.Basis.map_apply]
    change E (b (erel i)) =
      Algebra.Extension.Cotangent.mk
        ⟨P₂.relation i, P₂.relation_mem_ker i⟩
    rw [hb (erel i)]
    change Algebra.Extension.Cotangent.map H.toExtensionHom
        (Algebra.Extension.Cotangent.mk _) = _
    rw [Algebra.Extension.Cotangent.map_mk]
    apply congrArg (Algebra.Extension.Cotangent.mk (P := P₂.toExtension))
    apply Subtype.ext
    change H.toAlgHom (P₁.relation (erel i)) = P₂.relation i
    change MvPolynomial.aeval (MvPolynomial.X ∘ evar.symm)
        (P₁.relation (erel i)) =
      MvPolynomial.rename evar.symm (P₁.relation (erel i))
    rw [← MvPolynomial.rename_eq_aeval]

/-! ## Polynomial examples -/

/-- The monic polynomial with coefficient list `a₁, ..., aₙ`. -/
def monicPolynomial
    {A : Type u} [Semiring A] (n : ℕ) (a : Fin n → A) : Polynomial A :=
  Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)

private theorem monicPolynomial_degree
    {A : Type u} [Semiring A] [Nontrivial A] (n : ℕ) (a : Fin n → A) :
    (monicPolynomial n a).degree = n := by
  classical
  unfold monicPolynomial
  have hdeg := Polynomial.degree_sum_le (Finset.univ : Finset (Fin n))
    (fun i : Fin n => Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1))
  have hlt : (∑ i : Fin n, Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)).degree <
      (n : WithBot ℕ) := by
    apply lt_of_le_of_lt hdeg
    rw [Finset.sup_lt_iff]
    · intro i hi
      have hi' : i.1 < n := i.isLt
      have hnat : n - i.1 - 1 < n := by omega
      calc
        (Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)).degree ≤
            ((n - i.1 - 1 : ℕ) : WithBot ℕ) :=
          Polynomial.degree_C_mul_X_pow_le _ _
        _ < (n : WithBot ℕ) := WithBot.coe_lt_coe.mpr hnat
    · exact WithBot.bot_lt_coe n
  calc
    (Polynomial.X ^ n + ∑ i : Fin n,
        Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)).degree =
        (Polynomial.X ^ n).degree :=
      Polynomial.degree_add_eq_left_of_degree_lt (by
        rw [Polynomial.degree_X_pow]
        exact hlt)
    _ = n := by exact Polynomial.degree_X_pow n

private theorem monicPolynomial_monic
    {A : Type u} [Semiring A] (n : ℕ) (a : Fin n → A) :
    (monicPolynomial n a).Monic := by
  unfold monicPolynomial
  apply Polynomial.monic_X_pow_add
  have hdeg := Polynomial.degree_sum_le (Finset.univ : Finset (Fin n))
    (fun i : Fin n => Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1))
  apply lt_of_le_of_lt hdeg
  rw [Finset.sup_lt_iff]
  · intro i hi
    have hi' : i.1 < n := i.isLt
    have hnat : n - i.1 - 1 < n := by omega
    calc
      (Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)).degree ≤
          ((n - i.1 - 1 : ℕ) : WithBot ℕ) :=
        Polynomial.degree_C_mul_X_pow_le _ _
      _ < (n : WithBot ℕ) := WithBot.coe_lt_coe.mpr hnat
  · exact WithBot.bot_lt_coe n

private theorem monicPolynomial_eq_of_monic
    {A : Type u} [Semiring A] [Nontrivial A] (n : ℕ) (p : Polynomial A)
    (hp : p.Monic) (hdeg : p.degree = n) :
    monicPolynomial n (fun i => p.coeff (n - i.1 - 1)) = p := by
  unfold monicPolynomial
  conv_rhs => rw [hp.as_sum]
  have hnat : p.natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some hdeg
  rw [hnat]
  conv_rhs =>
    rw [← Fin.sum_univ_eq_sum_range
      (fun i : ℕ => Polynomial.C (p.coeff i) * Polynomial.X ^ i) n]
    rw [← Equiv.sum_comp Fin.revPerm]
  congr 1

private theorem monicPolynomial_coeff
    {A : Type u} [Semiring A] (n : ℕ) (a : Fin n → A) (k : Fin n) :
    (monicPolynomial n a).coeff (n - k.1 - 1) = a k := by
  classical
  unfold monicPolynomial
  change (Polynomial.X ^ n +
      ∑ i ∈ (Finset.univ : Finset (Fin n)),
        Polynomial.C (a i) * Polynomial.X ^ (n - i.1 - 1)).coeff
      (n - k.1 - 1) = a k
  rw [Polynomial.coeff_add, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow]
  have hklt : n - k.1 - 1 < n := by omega
  simp only [if_neg (Nat.ne_of_lt hklt), zero_add]
  have heq (x : Fin n) : n - k.1 - 1 = n - x.1 - 1 ↔ x = k := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      simpa [h]
  simp_rw [heq]
  simp

private theorem map_freeMonic_rev
    {R B : Type u} [CommRing R] [CommRing B] [Nontrivial R] [Nontrivial B]
    (n : ℕ) (φ : MvPolynomial (Fin n) R →+* B) (a : Fin n → B)
    (hφ : ∀ i, φ (MvPolynomial.X i) = a (Fin.revPerm i)) :
    Polynomial.map φ (Polynomial.freeMonic R n) = monicPolynomial n a := by
  have hp : (Polynomial.map φ (Polynomial.freeMonic R n)).Monic :=
    (Polynomial.monic_freeMonic R n).map φ
  have hd : (Polynomial.map φ (Polynomial.freeMonic R n)).degree = n := by
    rw [(Polynomial.monic_freeMonic R n).degree_map, Polynomial.degree_freeMonic]
  rw [← monicPolynomial_eq_of_monic n
    (Polynomial.map φ (Polynomial.freeMonic R n)) hp hd]
  congr 1
  funext i
  rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
  rw [dif_pos (by omega)]
  rw [hφ]
  congr 1
  have hi : (⟨n - i.1 - 1, by omega⟩ : Fin n) = Fin.revPerm i := by
    apply Fin.ext
    simp [Fin.revPerm_apply]
    omega
  rw [hi]
  simpa [Fin.revPerm] using (Fin.rev_involutive i)

abbrev FactorPolynomialBase (n m : ℕ) := MvPolynomial (Fin (n + m)) ℤ

abbrev FactorPolynomialTarget (n m : ℕ) :=
  MvPolynomial (Sum (Fin n) (Fin m)) ℤ

noncomputable def factorTargetPolynomial (n m : ℕ) :
    Polynomial (FactorPolynomialTarget n m) :=
  monicPolynomial n (fun i => MvPolynomial.X (Sum.inl i)) *
    monicPolynomial m (fun j => MvPolynomial.X (Sum.inr j))

noncomputable def factorPolynomialMap (n m : ℕ) :
    FactorPolynomialBase n m →ₐ[ℤ] FactorPolynomialTarget n m :=
  MvPolynomial.aeval (fun k =>
    (factorTargetPolynomial n m).coeff (n + m - k.1 - 1))

theorem factorPolynomialMap_spec (n m : ℕ) (k : Fin (n + m)) :
    factorPolynomialMap n m (MvPolynomial.X k) =
      (factorTargetPolynomial n m).coeff (n + m - k.1 - 1) := by
  simp [factorPolynomialMap]

theorem factorPolynomialMap_factorization (n m : ℕ) :
    Polynomial.map (factorPolynomialMap n m).toRingHom
        (monicPolynomial (n + m) (fun k => MvPolynomial.X k)) =
      factorTargetPolynomial n m := by
  have hp : (factorTargetPolynomial n m).Monic := by
    unfold factorTargetPolynomial
    exact
      (monicPolynomial_monic n
        (fun i : Fin n => MvPolynomial.X (Sum.inl i))).mul
        (monicPolynomial_monic m
          (fun j : Fin m => MvPolynomial.X (Sum.inr j)))
  have hdeg : (factorTargetPolynomial n m).degree = n + m := by
    unfold factorTargetPolynomial
    rw [(monicPolynomial_monic m
          (fun j : Fin m => MvPolynomial.X (Sum.inr j))).degree_mul]
    rw [monicPolynomial_degree, monicPolynomial_degree]
  rw [monicPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow]
  simp [factorPolynomialMap_spec]
  change monicPolynomial (n + m)
    (fun k => (factorTargetPolynomial n m).coeff (n + m - k.1 - 1)) =
      factorTargetPolynomial n m
  exact monicPolynomial_eq_of_monic (n + m) (factorTargetPolynomial n m) hp hdeg

theorem factorPolynomialMap_has_expected_presentation
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (factorPolynomialMap n m).toAlgebra
    ∃ (P : Formalization.Books.Algebra.Unit134.Presentation
      (FactorPolynomialBase n m) (FactorPolynomialTarget n m) (Fin (n + m)))
      (fs : Fin (n + m) → P.Ring),
      IsPolynomialQuotientPresentation P fs := by
  letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
    (factorPolynomialMap n m).toAlgebra
  let q0 := MvPolynomial.universalFactorizationMap ℤ (n + m) n m rfl
  let er := MvPolynomial.renameEquiv (R := ℤ)
    (σ := Fin (n + m)) (τ := Fin (n + m)) Fin.revPerm
  let q := q0.comp er.toAlgHom
  let esum := MvPolynomial.renameEquiv (R := ℤ)
    (σ := Sum (Fin n) (Fin m)) (τ := Sum (Fin n) (Fin m))
    (Equiv.sumCongr Fin.revPerm Fin.revPerm)
  let e0 := (MvPolynomial.tensorEquivSum ℤ (Fin n) (Fin m) ℤ).trans esum
  letI : Algebra (FactorPolynomialBase n m)
      (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) := q.toAlgebra
  let φ₁ : MvPolynomial (Fin n) ℤ →+* FactorPolynomialTarget n m :=
    e0.toRingHom.comp (algebraMap (MvPolynomial (Fin n) ℤ)
      (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ))
  have hφ₁ (i : Fin n) : φ₁ (MvPolynomial.X i) =
      MvPolynomial.X (Sum.inl (Fin.revPerm i)) := by
    simp [φ₁, e0, esum]
  have hleftpoly :
      Polynomial.map φ₁ (Polynomial.freeMonic ℤ n) =
        monicPolynomial n (fun i => MvPolynomial.X (Sum.inl i)) := by
    apply map_freeMonic_rev n φ₁
      (fun i => MvPolynomial.X (Sum.inl i))
    exact hφ₁
  let φ₂ : MvPolynomial (Fin m) ℤ →+* FactorPolynomialTarget n m :=
    e0.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        MvPolynomial (Fin m) ℤ →ₐ[ℤ]
          MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ).toRingHom
  have hφ₂ (i : Fin m) : φ₂ (MvPolynomial.X i) =
      MvPolynomial.X (Sum.inr (Fin.revPerm i)) := by
    simp [φ₂, e0, esum]
  have hrightpoly :
      Polynomial.map φ₂ (Polynomial.freeMonic ℤ m) =
        monicPolynomial m (fun i => MvPolynomial.X (Sum.inr i)) := by
    apply map_freeMonic_rev m φ₂
      (fun i => MvPolynomial.X (Sum.inr i))
    exact hφ₂
  have hleftmap :
      Polynomial.map e0.toRingHom
          (Polynomial.map (algebraMap (MvPolynomial (Fin n) ℤ)
            (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ))
            (Polynomial.freeMonic ℤ n)) =
        monicPolynomial n (fun i => MvPolynomial.X (Sum.inl i)) := by
    rw [Polynomial.map_map]
    exact hleftpoly
  have hrightmap :
      Polynomial.map e0.toRingHom
          (Polynomial.map
            ((Algebra.TensorProduct.includeRight :
              MvPolynomial (Fin m) ℤ →ₐ[ℤ]
                MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ).toRingHom)
            (Polynomial.freeMonic ℤ m)) =
        monicPolynomial m (fun i => MvPolynomial.X (Sum.inr i)) := by
    rw [Polynomial.map_map]
    exact hrightpoly
  have hprod :
      Polynomial.map e0.toRingHom
          (Polynomial.map (algebraMap (MvPolynomial (Fin n) ℤ)
            (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ))
            (Polynomial.freeMonic ℤ n) *
          Polynomial.map
            ((Algebra.TensorProduct.includeRight :
              MvPolynomial (Fin m) ℤ →ₐ[ℤ]
                MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ).toRingHom)
            (Polynomial.freeMonic ℤ m)) =
        factorTargetPolynomial n m := by
    rw [Polynomial.map_mul, hleftmap, hrightmap]
    rfl
  have hpoly :=
    MvPolynomial.universalFactorizationMap_freeMonic ℤ (n + m) n m rfl
  have hq : e0.toAlgHom.comp q = factorPolynomialMap n m := by
    apply MvPolynomial.algHom_ext
    intro k
    rw [factorPolynomialMap_spec]
    simp [q, er]
    have hk := congrArg
      (fun p : Polynomial (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) =>
        p.coeff (Fin.revPerm k).1) hpoly
    have hleft (k : Fin (n + m)) :
        e0 ((Polynomial.map q0 (Polynomial.freeMonic ℤ (n + m))).coeff
          (Fin.revPerm k).1) =
          e0 (q0 (MvPolynomial.X (Fin.revPerm k))) := by
      rw [Polynomial.coeff_map, Polynomial.coeff_freeMonic]
      rw [dif_pos (Fin.revPerm k).isLt]
      congr 1
    have hk' := congrArg (fun x => e0 x) hk
    rw [hleft k] at hk'
    have hkprod := congrArg
      (fun p : Polynomial (FactorPolynomialTarget n m) =>
        p.coeff (Fin.revPerm k).1) hprod
    rw [Polynomial.coeff_map] at hkprod
    convert hk'.trans hkprod using 1
    · rfl
    · congr 1
  let e : (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) ≃ₐ[FactorPolynomialBase n m]
      FactorPolynomialTarget n m :=
    { toRingEquiv := e0.toRingEquiv
      commutes' := by
        intro r
        change e0 (q r) = factorPolynomialMap n m r
        simpa using congrArg (fun F => F r) hq }
  let P₀ := MvPolynomial.universalFactorizationMapPresentation ℤ (n + m) n m rfl
  let rho : MvPolynomial (Sum (Fin n) (Fin m))
      (MvPolynomial (Fin (n + m)) ℤ) ≃ₐ[ℤ]
      MvPolynomial (Sum (Fin n) (Fin m)) (FactorPolynomialBase n m) :=
    MvPolynomial.mapAlgEquiv (Sum (Fin n) (Fin m)) er.symm
  let uval : Sum (Fin n) (Fin m) →
      MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ :=
    Sum.elim (fun i => MvPolynomial.X i ⊗ₜ[ℤ] 1)
      (fun j => 1 ⊗ₜ[ℤ] MvPolynomial.X j)
  let pval : MvPolynomial (Sum (Fin n) (Fin m))
      (MvPolynomial (Fin (n + m)) ℤ) →+*
      MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ :=
    letI : Algebra (MvPolynomial (Fin (n + m)) ℤ)
        (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) := q0.toAlgebra
    (MvPolynomial.aeval uval).toRingHom
  let valq : MvPolynomial (Sum (Fin n) (Fin m)) (FactorPolynomialBase n m) →ₐ[
      FactorPolynomialBase n m] FactorPolynomialTarget n m :=
    MvPolynomial.aeval (fun s => e (uval s))
  have hval : valq.toRingHom.comp rho.toRingHom =
      e.toRingHom.comp pval := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [valq, rho, pval, uval, er]
      change q (MvPolynomial.rename Fin.revPerm a) = q0 a
      simp [q, er, MvPolynomial.rename_rename, Fin.revPerm]
      have hrev : (Fin.rev ∘ Fin.rev : Fin (n + m) → Fin (n + m)) = id := by
        funext i
        simp [Fin.revPerm_apply]
      rw [hrev, MvPolynomial.rename_id_apply]
    · intro s
      simp [valq, rho, pval, P₀]
  have hsurj₀ : Function.Surjective pval := by
    intro y
    letI : Algebra (MvPolynomial (Fin (n + m)) ℤ)
        (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) := q0.toAlgebra
    have huval : P₀.val = uval := by
      funext s
      cases s <;> rfl
    obtain ⟨p, hp⟩ := P₀.toGenerators.aeval_val_surjective y
    refine ⟨p, ?_⟩
    change (MvPolynomial.aeval uval) p = y
    rw [← huval]
    exact hp
  have hsurj : Function.Surjective valq := by
    intro y
    obtain ⟨p, hp⟩ := hsurj₀ (e.symm y)
    refine ⟨rho p, ?_⟩
    change (valq.toRingHom.comp rho.toRingHom) p = y
    rw [hval]
    have hpy : e (pval p) = y := by
      rw [hp, e.apply_symm_apply]
    have hpy' : e.toRingEquiv.toRingHom (pval p) = y := hpy
    simpa only [RingHom.coe_comp, Function.comp_apply] using hpy'
  let Gq : Algebra.Generators (FactorPolynomialBase n m)
      (FactorPolynomialTarget n m) (Sum (Fin n) (Fin m)) :=
    Algebra.Generators.ofSurjective
      (fun s => e (uval s)) hsurj
  let rel₀ : Fin (n + m) →
      MvPolynomial (Sum (Fin n) (Fin m)) (MvPolynomial (Fin (n + m)) ℤ) :=
    fun i => MvPolynomial.C (MvPolynomial.X i) -
      (MvPolynomial.tensorEquivSum ℤ (Fin n) (Fin m) ℤ
        (q0 (MvPolynomial.X i))).map MvPolynomial.C
  let rel : Fin (n + m) → Gq.Ring :=
    fun i => rho (rel₀ (Fin.revPerm i))
  have hrel : Set.range rel = rho.toRingHom '' Set.range rel₀ := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨rel₀ (Fin.revPerm i), ⟨Fin.revPerm i, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := Fin.revPerm.surjective j
      simp [rel]
  have hmap : Ideal.map rho.toRingHom (Ideal.span (Set.range rel₀)) =
      Ideal.span (Set.range rel) := by
    rw [Ideal.map_span, hrel]
  have hker : Ideal.comap rho.toRingHom Gq.ker = RingHom.ker pval := by
    ext x
    change valq (rho x) = 0 ↔ pval x = 0
    have hx := congrArg
      (fun f : MvPolynomial (Sum (Fin n) (Fin m))
          (MvPolynomial (Fin (n + m)) ℤ) →+* FactorPolynomialTarget n m => f x) hval
    have hx' : valq.toRingHom (rho.toRingHom x) =
        e.toRingEquiv.toRingHom (pval x) := hx
    change valq.toRingHom (rho.toRingHom x) = 0 ↔ pval x = 0
    rw [hx']
    constructor
    · intro h
      apply e.toRingEquiv.injective
      simpa using h
    · intro h
      simpa [h]
  have hP₀span : Ideal.span (Set.range rel₀) = RingHom.ker pval := by
    letI : Algebra (MvPolynomial (Fin (n + m)) ℤ)
        (MvPolynomial (Fin n) ℤ ⊗[ℤ] MvPolynomial (Fin m) ℤ) := q0.toAlgebra
    change Ideal.span (Set.range rel₀) =
      RingHom.ker (MvPolynomial.eval₂Hom q0 uval)
    simpa [rel₀] using
      (MvPolynomial.ker_eval₂Hom_universalFactorizationMap ℤ (n + m) n m rfl).symm
  have hspan : Ideal.span (Set.range rel) = Gq.ker := by
    apply Ideal.comap_injective_of_surjective rho.toRingHom rho.surjective
    rw [← hmap]
    have hcm : Ideal.comap rho.toRingHom
        (Ideal.map rho.toRingHom (Ideal.span (Set.range rel₀))) =
        Ideal.span (Set.range rel₀) :=
      Ideal.comap_map_of_bijective _ rho.bijective
    rw [hcm]
    rw [hker]
    exact hP₀span
  let Pq : Algebra.Presentation (FactorPolynomialBase n m)
      (FactorPolynomialTarget n m) (Sum (Fin n) (Fin m)) (Fin (n + m)) :=
    { __ := Gq
      relation := rel
      span_range_relation_eq_ker := hspan }
  let Pq' := Pq.reindex (finSumFinEquiv.symm) (Equiv.refl (Fin (n + m)))
  let P : Formalization.Books.Algebra.Unit134.Presentation
      (FactorPolynomialBase n m) (FactorPolynomialTarget n m) (Fin (n + m)) :=
    Pq'.toGenerators
  let fs : Fin (n + m) → P.Ring := fun i => Pq'.relation i
  refine ⟨P, fs, ?_⟩
  change Pq'.ker = Ideal.ofList (List.ofFn fs)
  rw [← Pq'.span_range_relation_eq_ker]
  change Ideal.span (Set.range Pq'.relation) =
    Ideal.ofList (List.ofFn fs)
  rw [Ideal.ofList]
  congr 1
  ext x
  simp [fs]

theorem factorPolynomialMap_fibre_dimension_zero
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (p : PrimeSpectrum (FactorPolynomialBase n m)) :
    letI : Algebra (FactorPolynomialBase n m) (FactorPolynomialTarget n m) :=
      (factorPolynomialMap n m).toAlgebra
    Nonempty (PrimeSpectrum
        (p.asIdeal.Fiber (FactorPolynomialTarget n m))) →
      ringKrullDim
          (p.asIdeal.Fiber (FactorPolynomialTarget n m)) = 0 := by
  sorry

theorem factorPolynomialMap_is_finite
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    RingHom.Finite (factorPolynomialMap n m).toRingHom := by
  sorry

theorem factorPolynomialMap_is_integral
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (factorPolynomialMap n m).toRingHom.IsIntegral := by
  sorry

theorem factorPolynomialMap_is_relative_global_complete_intersection
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    IsRelativeGlobalCompleteIntersection (factorPolynomialMap n m).toRingHom := by
  sorry

/-! ## The universal polynomial and its roots -/

abbrev RootsPolynomialBase (n : ℕ) := MvPolynomial (Fin n) ℤ

/- The empty summand keeps the target's root variables distinct from the
   coefficient variables while still giving exactly `n` root variables. -/
abbrev RootsPolynomialTarget (n : ℕ) :=
  MvPolynomial (Sum (Fin n) Empty) ℤ

def elementarySymmetric
    {A : Type u} [CommRing A] (n k : ℕ) (a : Fin n → A) : A :=
  (Finset.univ.powerset.filter (fun t => t.card = k)).sum
    (fun t => t.prod a)

noncomputable def rootsPolynomialMap (n : ℕ) :
    RootsPolynomialBase n →ₐ[ℤ] RootsPolynomialTarget n :=
  MvPolynomial.aeval (fun k =>
    elementarySymmetric (n := n) (k.1 + 1)
      (fun i => MvPolynomial.X (Sum.inl i)))

noncomputable def rootsTargetPolynomial (n : ℕ) :
  Polynomial (RootsPolynomialTarget n) :=
  ∏ i : Fin n, (Polynomial.X +
    Polynomial.C (MvPolynomial.X (Sum.inl i)))

def RootMonomialIndex (n : ℕ) :=
  ∀ i : Fin n, Fin (n - i.1)

def rootMonomial (n : ℕ) (e : RootMonomialIndex n) :
    RootsPolynomialTarget n :=
  ∏ i : Fin n, MvPolynomial.X (Sum.inl i) ^ (e i).1

theorem rootsPolynomialMap_spec (n : ℕ) (k : Fin n) :
    rootsPolynomialMap n (MvPolynomial.X k) =
      elementarySymmetric (n := n) (k.1 + 1)
        (fun i => MvPolynomial.X (Sum.inl i)) := by
  sorry

theorem rootsPolynomial_factorization (n : ℕ) :
    Polynomial.map (rootsPolynomialMap n).toRingHom
        (monicPolynomial n (fun k => MvPolynomial.X k)) =
      rootsTargetPolynomial n := by
  sorry

theorem rootsPolynomialMap_finite_free
    {n : ℕ} :
    letI : Algebra (RootsPolynomialBase n) (RootsPolynomialTarget n) :=
      (rootsPolynomialMap n).toAlgebra
    Module.Finite (RootsPolynomialBase n) (RootsPolynomialTarget n) ∧
      Module.Free (RootsPolynomialBase n) (RootsPolynomialTarget n) ∧
      (∃ b : Basis (RootMonomialIndex n) (RootsPolynomialBase n)
          (RootsPolynomialTarget n),
        ∀ e, b e = rootMonomial n e) := by
  sorry

theorem rootsPolynomialMap_is_finite_faithfully_flat
    {n : ℕ} :
    RingHom.Finite (rootsPolynomialMap n).toRingHom ∧
      RingHom.FaithfullyFlat (rootsPolynomialMap n).toRingHom := by
  sorry

theorem rootsPolynomialMap_fibre_dimension_zero
    {n : ℕ} (p : PrimeSpectrum (RootsPolynomialBase n)) :
    letI : Algebra (RootsPolynomialBase n) (RootsPolynomialTarget n) :=
      (rootsPolynomialMap n).toAlgebra
    Nonempty (PrimeSpectrum
        (p.asIdeal.Fiber (RootsPolynomialTarget n))) →
      ringKrullDim
          (p.asIdeal.Fiber (RootsPolynomialTarget n)) = 0 := by
  sorry

theorem rootsPolynomialMap_is_relative_global_complete_intersection
    {n : ℕ} :
    IsRelativeGlobalCompleteIntersection (rootsPolynomialMap n).toRingHom := by
  sorry

/-! ## Base change, localization, approximation, and conormal modules -/

theorem localize_relative_complete_intersection
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring) (hc : c ≤ n),
      IsPolynomialQuotientPresentation P fs →
      ∀ (I : Ideal R),
      HasFiberDimension
        (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)
          (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) →
      ∃ (g : S) (h : P.Ring),
        algebraMap P.Ring S h = g ∧
          Ideal.Quotient.mk (Ideal.map f I) g = 1 ∧
          IsRelativeGlobalCompleteIntersection
            (algebraMap R (Localization.Away g)) := by
  sorry

theorem localize_relative_complete_intersection_at_fibre
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring) (hc : c ≤ n),
      IsPolynomialQuotientPresentation P fs →
      (p : PrimeSpectrum R) →
      (hdim : ringKrullDim (Fiber R S p) =
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) →
    ∃ (g : S) (h : P.Ring),
      algebraMap P.Ring S h = g ∧
        IsUnitInFiber f p g ∧
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g)) := by
  sorry

theorem localize_relative_complete_intersection_at_prime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    : letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring) (hc : c ≤ n),
      IsPolynomialQuotientPresentation P fs →
      (p : PrimeSpectrum R) → (q' : PrimeSpectrum P.Ring) →
      (q : PrimeSpectrum S) →
      (hlying : PrimeSpectrum.comap f q = p) →
      (hq : PrimeSpectrum.comap (algebraMap P.Ring S) q = q') →
      (hdim : LocalFiberDimensionAt f p q hlying =
      (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞)) →
    ∃ (g : S) (h : P.Ring),
      algebraMap P.Ring S h = g ∧
        g ∉ q.asIdeal ∧
        IsRelativeGlobalCompleteIntersection
          (algebraMap R (Localization.Away g)) := by
  sorry

def NoetherianApproximationData
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n c : ℕ}
    (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
    (fs : Fin c → P.Ring) : Prop :=
  ∃ (R₀ : Subalgebra ℤ R) (fs₀ : Fin c → MvPolynomial (Fin n) R₀),
    RingHom.FiniteType (algebraMap ℤ R₀) ∧
      (∀ i, MvPolynomial.map R₀.val (fs₀ i) = fs i) ∧
      let Q := MvPolynomial (Fin n) R₀ ⧸ Ideal.ofList (List.ofFn fs₀)
      letI : CommRing Q := Ideal.Quotient.commRing _
      IsRelativeGlobalCompleteIntersection (algebraMap R₀ Q)

theorem relative_global_complete_intersection_noetherian_approximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hrel : IsRelativeGlobalCompleteIntersection f) :
    letI : Algebra R S := f.toAlgebra
    ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring),
      IsPolynomialQuotientPresentation P fs →
      NoetherianApproximationData P fs := by
  sorry

def PrefixRelations {A : Type u} [AddMonoid A]
    {c : ℕ} (fs : Fin c → A) (i : ℕ) (hi : i ≤ c) : List A :=
  List.ofFn (fun j : Fin i => fs ⟨j.1, lt_of_lt_of_le j.isLt hi⟩)

def LocalFiberMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) :
    R →+* Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying :=
  (Ideal.Quotient.mk
      (Formalization.Books.Algebra.Unit112.fibreIdealInLocalization f p q)).comp
    ((algebraMap S (Localization.AtPrime q.asIdeal)).comp f)

def IsCompleteIntersectionOverResidueField
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) : Prop :=
  let L := Formalization.Books.Algebra.Unit112.localRingOfFibre f p q hlying
  letI : Algebra R L := (LocalFiberMap f p q hlying).toAlgebra
  ∃ hL : IsLocalRing L, ∃ hKL : Algebra p.asIdeal.ResidueField L,
    letI : IsLocalRing L := hL
    letI : Algebra p.asIdeal.ResidueField L := hKL
    IsScalarTower R p.asIdeal.ResidueField L ∧
      Formalization.Books.Algebra.Unit135.IsCompleteIntersection
        p.asIdeal.ResidueField L

def FlatQuotientOfRingHom
    {R L : Type u} [CommRing R] [CommRing L]
    (I : Ideal L) (b : R →+* L) : Prop :=
  RingHom.Flat ((Ideal.Quotient.mk I).comp b)

theorem relative_global_complete_intersection_conormal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    :
    letI : Algebra R S := f.toAlgebra
      ∀ {n c : ℕ}
      (P : Formalization.Books.Algebra.Unit134.Presentation R S (Fin n))
      (fs : Fin c → P.Ring) (hc : c ≤ n),
      IsPolynomialQuotientPresentation P fs →
      HasFiberDimension f
        (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) →
      (q : PrimeSpectrum S) → (q' : PrimeSpectrum P.Ring) →
      PrimeSpectrum.comap (algebraMap P.Ring S) q = q' →
    RingTheory.Sequence.IsRegular (Localization.AtPrime q'.asIdeal)
        (List.ofFn (fun i =>
          algebraMap P.Ring (Localization.AtPrime q'.asIdeal) (fs i))) ∧
      (∀ (i : ℕ) (hi : i ≤ c),
        FlatQuotientOfRingHom
          (Ideal.map (algebraMap P.Ring (Localization.AtPrime q'.asIdeal))
            (Ideal.ofList (PrefixRelations fs i hi)))
          (algebraMap R (Localization.AtPrime q'.asIdeal))) ∧
      HasConormalBasisPresentation P fs := by
  sorry

theorem relative_global_complete_intersection_is_syntomic
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hrel : IsRelativeGlobalCompleteIntersection f) :
    IsSyntomic f := by
  sorry

/-! ## Finite free root extensions -/

def PolynomialSplitsIntoRoots
    {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') {n : ℕ} (P : Polynomial A) (β : Fin n → A') : Prop :=
  Polynomial.map f P =
    ∏ i : Fin n, (Polynomial.X - Polynomial.C (β i) : Polynomial A')

theorem adjoin_roots
    {A : Type u} [CommRing A] (n : ℕ) (b : Fin n → A) :
    ∃ (A' : Type u) (hA' : CommRing A'),
      letI : CommRing A' := hA'
      ∃ (f : A →+* A'),
        letI : Algebra A A' := f.toAlgebra
        ∃ (β : Fin n → A'),
        IsSyntomic f ∧
            Module.Finite A A' ∧ Module.Free A A' ∧
            RingHom.FaithfullyFlat f ∧
              PolynomialSplitsIntoRoots f (monicPolynomial n b) β := by
  sorry

/-! ## The local criterion for syntomicity -/

def IsFlatAtPrime
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (_hlying : PrimeSpectrum.comap f q = p) : Prop :=
  letI : Algebra R S := f.toAlgebra
  let hcomap : p.asIdeal = q.asIdeal.comap f := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      (congrArg PrimeSpectrum.asIdeal _hlying).symm
  RingHom.Flat (Localization.localRingHom p.asIdeal q.asIdeal f hcomap)

theorem syntomic_local_criterion
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hlying : PrimeSpectrum.comap f q = p) :
    letI : Algebra R S := f.toAlgebra
    List.TFAE
      [ (∃ g : S, g ∉ q.asIdeal ∧
          IsSyntomic (algebraMap R (Localization.Away g))),
        (∃ g : S, g ∉ q.asIdeal ∧
          IsRelativeGlobalCompleteIntersection
            (algebraMap R (Localization.Away g))),
        (∃ g : S, g ∉ q.asIdeal ∧
          RingHom.FinitePresentation (algebraMap R (Localization.Away g)) ∧
          IsFlatAtPrime f p q hlying ∧
          IsCompleteIntersectionOverResidueField f p q hlying) ] := by
  sorry

/-! ## Conormal modules and composition -/

theorem syntomic_presentation_ideal_mod_squares
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    :
    letI : Algebra R S := f.toAlgebra
    ∀ {n : ℕ} (P : Formalization.Books.Algebra.Unit134.Presentation
      R S (Fin n))
      (hP : RingHom.FinitePresentation (algebraMap P.Ring S)) (g : S),
    IsSyntomic (algebraMap R (Localization.Away g)) →
    Formalization.Books.Algebra.Unit78.FiniteProjective
      (Localization.Away g)
      (LocalizedModule.Away g P.toExtension.Cotangent) := by
  sorry

theorem composition_relative_global_complete_intersection
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsRelativeGlobalCompleteIntersection f)
    (hg : IsRelativeGlobalCompleteIntersection g) :
    IsRelativeGlobalCompleteIntersection (g.comp f) := by
  sorry

theorem composition_syntomic
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : IsSyntomic f) (hg : IsSyntomic g) :
    IsSyntomic (g.comp f) := by
  sorry

/-! ## Lifting a syntomic map through a quotient -/

def SyntomicLiftPiece
    {R Sbar : Type u} [CommRing R] [CommRing Sbar]
    (J : Ideal R) (fbar : (R ⧸ J) →+* Sbar) (g : Sbar) : Prop :=
  letI : Algebra (R ⧸ J) Sbar := fbar.toAlgebra
    ∃ (T : Type u) (hT : CommRing T) (f : R →+* T),
    letI : CommRing T := hT
    IsRelativeGlobalCompleteIntersection f ∧
      ∃ e : (T ⧸ Ideal.map f J) ≃+* Localization.Away g,
        e.toRingHom.comp
              (Ideal.quotientMap (Ideal.map f J) f Ideal.le_comap_map) =
            algebraMap (R ⧸ J) (Localization.Away g)

theorem lift_syntomic
    {R S : Type u} [CommRing R] [CommRing S] (J : Ideal R)
    (fbar : (R ⧸ J) →+* S)
    (hfbar : IsSyntomic fbar) :
    ∃ (m : ℕ) (gs : Fin m → S),
      Ideal.span (Set.range gs) = (⊤ : Ideal S) ∧
      (∀ i, SyntomicLiftPiece J fbar (gs i)) := by
  sorry

end

end Formalization.Books.Algebra.Unit136
