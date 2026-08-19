import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Commutative Algebra, Chapter 54: Homomorphisms essentially of finite type

The source's essentially finite type condition is Mathlib's canonical
`RingHom.EssFiniteType` predicate.  Mathlib does not currently provide the
analogous essentially finite presentation predicate, so the source's second
definition is represented by the explicit intermediate-algebra predicate
below.
-/

namespace Formalization.Books.Algebra.Unit54

open scoped TensorProduct

universe u v

/-! ## Definitions -/

/- The source's first definition is exactly `RingHom.EssFiniteType`; no
   parallel predicate is introduced. -/

/- The source's second definition allows an arbitrary intermediate algebra:
   its map to the target need not be injective before localization. -/
def essFinitePresentation
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (T : Type (max u v)) (hT : CommRing T),
    letI : CommRing T := hT
    ∃ (g : R →+* T) (M : Submonoid T) (q : T →+* S),
      RingHom.FinitePresentation g ∧
        q.comp g = algebraMap R S ∧
          letI : Algebra T S := q.toAlgebra
          IsLocalization M S

/- The ring-hom version uses the algebra structure induced by the map, just as
   Mathlib's `RingHom.EssFiniteType` does. -/
def RingHom.EssFinitePresentation
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  essFinitePresentation R S

/- A quotient followed by a localization, with the displayed map retained,
   is the source-facing form needed in the final lemma. -/
def RingHom.IsLocalizationOfQuotient
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∃ (I : Ideal A) (M : Submonoid (A ⧸ I)) (q : (A ⧸ I) →+* B),
    q.comp (Ideal.Quotient.mk I) = f ∧
      letI : Algebra (A ⧸ I) B := q.toAlgebra
      IsLocalization M B

/-! ## Composition and base change -/

/- Mathlib supplies the composition and base-change interfaces for essentially
   finite type ring homomorphisms. -/
theorem essFiniteType_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.EssFiniteType f) (hg : RingHom.EssFiniteType g) :
    RingHom.EssFiniteType (g.comp f) := by
  exact RingHom.EssFiniteType.comp hf hg

theorem essFiniteType_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.EssFiniteType :=
  RingHom.EssFiniteType.isStableUnderBaseChange

private theorem essFinitePresentation_respectsIso :
    RingHom.RespectsIso @RingHom.EssFinitePresentation := by
  constructor
  · intro R S T _ _ _ f e hf
    let : Algebra R S := f.toAlgebra
    change essFinitePresentation R S at hf
    rcases hf with ⟨A, hA, g, M, q, hq, hcomp, hloc⟩
    let : CommRing A := hA
    let q' := e.toRingHom.comp q
    let : Algebra A S := q.toAlgebra
    let : Algebra A T := q'.toAlgebra
    let : Algebra R T := (e.toRingHom.comp f).toAlgebra
    let e' : S ≃ₐ[A] T :=
      { toRingEquiv := e
        commutes' := by intro a; rfl }
    change essFinitePresentation R T
    refine ⟨A, hA, g, M, q', hq, ?_, ?_⟩
    · dsimp [q']
      rw [RingHom.comp_assoc, hcomp]
      rfl
    · exact IsLocalization.isLocalization_of_algEquiv M e'
  · intro R S T _ _ _ f e hf
    let : Algebra S T := f.toAlgebra
    change essFinitePresentation S T at hf
    rcases hf with ⟨A, hA, g, M, q, hq, hcomp, hloc⟩
    let : CommRing A := hA
    let g' := g.comp e.toRingHom
    let : Algebra A T := q.toAlgebra
    let : Algebra R T := (f.comp e.toRingHom).toAlgebra
    change essFinitePresentation R T
    refine ⟨A, hA, g', M, q,
      RingHom.FinitePresentation.comp hq (RingHom.FinitePresentation.of_bijective e.bijective),
      ?_, hloc⟩
    · dsimp [g']
      rw [← RingHom.comp_assoc, hcomp]
      rfl

/- The corresponding assertions for essentially finite presentation are
   recorded with the source's predicate. -/
theorem essFinitePresentation_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.EssFinitePresentation f)
    (hg : RingHom.EssFinitePresentation g) :
    RingHom.EssFinitePresentation (g.comp f) := by
  sorry
/-
  classical
  algebraize [f, g, g.comp f]
  change essFinitePresentation R S at hf
  change essFinitePresentation S T at hg
  rcases hf with ⟨Aorig, hAorig, aorig, Morig, qorig, hqorig, hqaorig, hlocorig⟩
  rcases hg with ⟨B, hB, b, N, r, hb, hbr, hloc'⟩
  letI : CommRing Aorig := hAorig
  letI : CommRing B := hB
  letI : Algebra Aorig S := qorig.toAlgebra
  letI : IsLocalization Morig S := hlocorig
  letI : Algebra R Aorig := aorig.toAlgebra
  letI : Algebra.FinitePresentation R Aorig := hqorig
  obtain ⟨k, e, he, hker⟩ := Algebra.FinitePresentation.out (R := R) (A := Aorig)
  let P0 := MvPolynomial (Fin k) R
  let I0 : Ideal P0 := RingHom.ker e.toRingHom
  let A := P0 ⧸ I0
  letI : CommRing A := by
    dsimp [A]
    infer_instance
  let e0 : A ≃+* Aorig := RingHom.quotientKerEquivOfSurjective he
  let mk0 : P0 →+* A := Ideal.Quotient.mk I0
  let a : R →+* A := mk0.comp (algebraMap R P0)
  let M : Submonoid A := Morig.map e0.symm
  let q : A →+* S := qorig.comp e0.toRingHom
  letI : Algebra A S := q.toAlgebra
  have hmk0 : RingHom.FinitePresentation mk0 := by
    apply RingHom.FinitePresentation.of_surjective mk0 Ideal.Quotient.mk_surjective
    rw [show RingHom.ker mk0 = I0 by
      dsimp [mk0]
      exact Ideal.mk_ker]
    exact hker
  have hP0 : RingHom.FinitePresentation (algebraMap R P0) := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  have hq : RingHom.FinitePresentation a := hmk0.comp hP0
  have hqa : q.comp a = algebraMap R S := by
    apply RingHom.ext
    intro x
    change qorig (e0 (mk0 (algebraMap R P0 x))) = algebraMap R S x
    rw [show e0 (mk0 (algebraMap R P0 x)) = e (algebraMap R P0 x) by
      exact RingHom.quotientKerEquivOfSurjective_apply_mk he _]
    rw [show e (algebraMap R P0 x) = aorig x by
      exact e.commutes x]
    exact DFunLike.congr_fun hqaorig x
  have hloc : IsLocalization M S := by
    convert IsLocalization.isLocalization_of_base_ringEquiv Morig S e0.symm using 1
    apply Algebra.algebra_ext
    intro x
    rfl
  letI : IsLocalization M S := hloc
  letI : Algebra B T := r.toAlgebra
  letI : Algebra S T := g.toAlgebra
  letI : Algebra R S := f.toAlgebra
  letI : Algebra S B := b.toAlgebra
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_eq' (by rw [← hbr]; rfl)
  letI : Algebra.FinitePresentation S B := hb
  obtain ⟨n, p, hp, hK⟩ := Algebra.FinitePresentation.out (R := S) (A := B)
  let P := MvPolynomial (Fin n) A
  let Q := MvPolynomial (Fin n) S
  let F : P →+* Q := MvPolynomial.map q
  letI : Algebra P Q := F.toAlgebra
  letI : IsLocalization (M.map (MvPolynomial.C : A →+* P)) Q :=
    MvPolynomial.isLocalization M S
  let K : Ideal Q := RingHom.ker p.toRingHom
  obtain ⟨s, hs⟩ := hK
  choose t ht using fun x : s =>
    IsLocalization.surj (M := M.map (MvPolynomial.C : A →+* P)) x.1
  let u : s → P := fun x => (t x).1
  let v : s → M.map (MvPolynomial.C : A →+* P) := fun x => (t x).2
  have huv (x : s) : x.1 * algebraMap P Q (v x) = algebraMap P Q (u x) := by
    exact ht x
  let uf : Finset P := Finset.univ.image u
  let I : Ideal P := Ideal.span (uf : Set P)
  have huI (x : s) : u x ∈ I := by
    apply Ideal.subset_span
    simp [I, uf]
  have hxK (x : s) : x.1 ∈ K := by
    change x.1 ∈ RingHom.ker p.toRingHom
    rw [← hs]
    exact Ideal.subset_span x.2
  have hu (x : s) : (p.toRingHom.comp F) (u x) = 0 := by
    have hpx : p x.1 = 0 := hxK x
    have hpu : p (algebraMap P Q (u x)) = 0 := by
      rw [← huv x, map_mul, hpx, zero_mul]
    exact hpu
  let L : P →+* B := p.toRingHom.comp F
  have hI : I ≤ RingHom.ker L := by
    change Ideal.span (uf : Set P) ≤ RingHom.ker L
    refine Ideal.span_le.2 ?_
    intro z hz
    simp only [uf, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨x, rfl⟩ := hz
    exact hu x
  let C := P ⧸ I
  letI : CommRing C := by
    dsimp [C]
    infer_instance
  let c : C →+* B := Ideal.Quotient.lift I L hI
  have hc : c.comp (Ideal.Quotient.mk I) = L := by
    apply RingHom.ext
    intro x
    exact Ideal.Quotient.lift_mk I L hI
  letI : Algebra C B := c.toAlgebra
  have hH : p.toRingHom.comp (algebraMap P Q) =
      (algebraMap C B).comp (Ideal.Quotient.mk I) := by
    apply RingHom.ext
    intro x
    change p (F x) = (Ideal.Quotient.lift I L hI) (Ideal.Quotient.mk I x)
    rfl
  have hH' : RingHom.ker p.toRingHom ≤
      (RingHom.ker (Ideal.Quotient.mk I)).map (algebraMap P Q) := by
    rw [Ideal.mk_ker]
    change RingHom.ker p.toRingHom ≤ I.map (algebraMap P Q)
    rw [← hs]
    refine Ideal.span_le.2 ?_
    intro z hz
    let x : s := ⟨z, hz⟩
    apply (IsLocalization.mem_map_algebraMap_iff (M.map (MvPolynomial.C : A →+* P)) Q).2
    exact ⟨⟨(⟨u x, huI x⟩ : I), v x⟩, huv x⟩
  have hlocB : IsLocalization
      ((M.map (MvPolynomial.C : A →+* P)).map (Ideal.Quotient.mk I)) B := by
    apply IsLocalization.of_surjective (M.map (MvPolynomial.C : A →+* P)) Q
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective p.toRingHom hp hH hH'
  have hC : RingHom.FinitePresentation (MvPolynomial.C : A →+* P) := by
    rw [← MvPolynomial.algebraMap_eq, RingHom.finitePresentation_algebraMap]
    infer_instance
  let aP : R →+* P := (MvPolynomial.C : A →+* P).comp a
  have haP : RingHom.FinitePresentation aP := by
    exact hC.comp hq
  let mk : P →+* C := Ideal.Quotient.mk I
  have hIFG : I.FG := ⟨uf, rfl⟩
  have hmk : RingHom.FinitePresentation mk := by
    apply RingHom.FinitePresentation.of_surjective mk Ideal.Quotient.mk_surjective
    rw [show RingHom.ker mk = I by
      dsimp [mk]
      exact Ideal.mk_ker]
    exact hIFG
  let d : R →+* C := mk.comp aP
  have hd : RingHom.FinitePresentation d := hmk.comp haP
  have hL : L.comp aP = (b.comp q).comp a := by
    apply RingHom.ext
    intro x
    change p (F (aP x)) = b (q (a x))
    simp only [F, aP, RingHom.comp_apply, MvPolynomial.map_C]
    simpa only [MvPolynomial.algebraMap_eq] using p.commutes (q (a x))
  have hcomp : (r.comp c).comp d = algebraMap R T := by
    apply RingHom.ext
    intro x
    change r (c (mk (aP x))) = algebraMap R T x
    have hcmk : c (mk (aP x)) = L (aP x) :=
      DFunLike.congr_fun hc (aP x)
    have hLx : L (aP x) = b (q (a x)) := DFunLike.congr_fun hL x
    calc
      r (c (mk (aP x))) = r (L (aP x)) := congrArg r hcmk
      _ = r (b (q (a x))) := congrArg r hLx
      _ = algebraMap S T (q (a x)) := DFunLike.congr_fun hbr (q (a x))
      _ = algebraMap R T x := by
        have hqax : q (a x) = algebraMap R S x := by
          simpa only [RingHom.comp_apply] using DFunLike.congr_fun hqa x
        rw [hqax]
        exact (IsScalarTower.algebraMap_apply R S T x).symm
  let U : Submonoid C :=
    (M.map (MvPolynomial.C : A →+* P)).map (Ideal.Quotient.mk I)
  letI : IsLocalization U B := hlocB
  letI : IsLocalization N T := hloc'
  letI : Algebra C T := (r.comp c).toAlgebra
  letI : IsScalarTower C B T :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  have hlocT : IsLocalization
      (IsLocalization.localizationLocalizationSubmodule U N) T :=
    IsLocalization.localization_localization_isLocalization U N T
  let C' := ULift.{u_3} C
  let eLift : C' ≃+* C := ULift.ringEquiv
  let dLift : R →+* C' := eLift.symm.toRingHom.comp d
  let qLift : C' →+* T := (r.comp c).comp eLift.toRingHom
  letI : Algebra C' T := qLift.toAlgebra
  have hlocLift : IsLocalization (U.map eLift.symm.toRingHom) T := by
    convert IsLocalization.isLocalization_of_base_ringEquiv
      (IsLocalization.localizationLocalizationSubmodule U N) T eLift.symm using 1
    apply Algebra.algebra_ext
    intro x
    rfl
  have hdLift : RingHom.FinitePresentation dLift := by
    apply RingHom.FinitePresentation.comp
      (RingHom.FinitePresentation.of_bijective eLift.symm.toRingHom eLift.symm.bijective)
    exact hd
  have hcompLift : qLift.comp dLift = algebraMap R T := by
    apply RingHom.ext
    intro x
    change (r.comp c) (eLift (eLift.symm (d x))) = algebraMap R T x
    rw [eLift.apply_symm_apply]
    exact DFunLike.congr_fun hcomp x
  change essFinitePresentation R T
  refine ⟨C', inferInstance, dLift, U.map eLift.symm.toRingHom, qLift,
    hdLift, hcompLift, hlocLift⟩ -/

theorem essFinitePresentation_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.EssFinitePresentation := by
  apply RingHom.IsStableUnderBaseChange.mk essFinitePresentation_respectsIso
  intros R S T _ _ _ _ _ h
  change essFinitePresentation R T at h
  rcases h with ⟨A, hA, g, M, q, hq, hcomp, hloc⟩
  let : CommRing A := hA
  let : Algebra R A := g.toAlgebra
  let : Algebra A T := q.toAlgebra
  let : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' (by
    rw [← hcomp]
    rfl)
  let qₐ : A →ₐ[R] T := IsScalarTower.toAlgHom R A T
  let q' : (S ⊗[R] A) →+* (S ⊗[R] T) :=
    (Algebra.TensorProduct.map (AlgHom.id S S) qₐ).toRingHom
  let : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra A (S ⊗[R] T) :=
    (Algebra.TensorProduct.includeRight.comp qₐ).toRingHom.toAlgebra
  let : Algebra (S ⊗[R] A) (S ⊗[R] T) := q'.toAlgebra
  let : IsScalarTower A (S ⊗[R] A) (S ⊗[R] T) := by
    apply IsScalarTower.of_algebraMap_eq'
    exact congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_restrictScalars_comp_includeRight
        (AlgHom.id S S) qₐ)
  let : Algebra.FinitePresentation R A := hq
  have hloc' : IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (S ⊗[R] T) := by
    apply IsLocalization.tensorProduct_tensorProduct_right R S M T
    exact congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_restrictScalars_comp_includeRight
        (AlgHom.id S S) qₐ)
  have hq' : RingHom.FinitePresentation (algebraMap S (S ⊗[R] A)) := by
    rw [RingHom.finitePresentation_algebraMap]
    infer_instance
  refine ⟨S ⊗[R] A, inferInstance, algebraMap S (S ⊗[R] A),
    M.map (Algebra.TensorProduct.includeRight (R := R) (A := S)), q', hq', ?_, hloc'⟩
  simp [q', RingHom.algebraMap_toAlgebra]

/-! ## Essentially finite type maps into Artinian local rings -/

/- The three numbered assertions in the source lemma are kept as separate
   equivalences so that each finiteness notion can be used independently. -/
theorem finite_iff_finite_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.Finite f ↔
      RingHom.Finite ((Ideal.Quotient.mk m).comp f) := by
  algebraize [f, (Ideal.Quotient.mk m).comp f]
  let : Algebra R (S ⧸ m) := ((Ideal.Quotient.mk m).comp f).toAlgebra
  refine ⟨?_, ?_⟩
  · intro hf
    exact RingHom.Finite.comp
      (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) hf
  · intro hf
    change Module.Finite R (S ⧸ m) at hf
    let : Module.Finite R (S ⧸ m) := hf
    exact Module.finite_of_surjective_of_ker_le_nilradical
      (Ideal.Quotient.mkₐ R m) Ideal.Quotient.mk_surjective (by
        change RingHom.ker (Ideal.Quotient.mkₐ R m : S →+* S ⧸ m) ≤ nilradical S
        rw [Ideal.Quotient.mkₐ_ker, IsLocalRing.eq_maximalIdeal (inferInstance : m.IsMaximal)]
        rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
      ) (by
        rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker,
          IsLocalRing.eq_maximalIdeal (inferInstance : m.IsMaximal)]
        exact Ideal.fg_of_isNoetherianRing _)

theorem finiteType_iff_finiteType_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.FiniteType f ↔
      RingHom.FiniteType ((Ideal.Quotient.mk m).comp f) := by
  algebraize [f, (Ideal.Quotient.mk m).comp f]
  let : Algebra R (S ⧸ m) := ((Ideal.Quotient.mk m).comp f).toAlgebra
  refine ⟨?_, ?_⟩
  · intro hf
    exact RingHom.FiniteType.comp
      (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hf
  · intro hf
    obtain ⟨n, a, ha⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
    choose b hb using fun i : Fin n =>
      Ideal.Quotient.mk_surjective (a (MvPolynomial.X i))
    let p : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval b
    let q : S →ₐ[R] S ⧸ m :=
      { toRingHom := Ideal.Quotient.mk m
        commutes' := by
          intro r
          rfl }
    have hp : q.comp p = a := by
      apply MvPolynomial.algHom_ext
      intro i
      simpa [AlgHom.comp_apply, q, p] using hb i
    have hpfinres : RingHom.Finite
        ((Ideal.Quotient.mk m).comp p.toRingHom) := by
      have hpeq : (Ideal.Quotient.mk m).comp p.toRingHom = a.toRingHom := by
        change q.toRingHom.comp p.toRingHom = a.toRingHom
        exact congrArg AlgHom.toRingHom hp
      rw [hpeq]
      exact RingHom.Finite.of_surjective _ ha
    have hpfin : RingHom.Finite p.toRingHom := by
      apply (finite_iff_finite_residue p.toRingHom m).mpr
      exact hpfinres
    have hpft : RingHom.FiniteType p.toRingHom := hpfin.to_finiteType
    have hi : RingHom.FiniteType (algebraMap R (MvPolynomial (Fin n) R)) := by
      rw [RingHom.finiteType_algebraMap]
      infer_instance
    have hcomp := RingHom.FiniteType.comp hpft hi
    have heq : p.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) = f := by
      ext r
      change p (algebraMap R (MvPolynomial (Fin n) R) r) = algebraMap R S r
      exact p.commutes r
    rw [heq] at hcomp
    exact hcomp

private theorem isLocalizationOfQuotient_of_isLocalization
    {P S : Type*} [CommRing P] [CommRing S] (p : P →+* S)
    (M : Submonoid P)
    (hloc : letI : Algebra P S := p.toAlgebra; IsLocalization M S) :
    RingHom.IsLocalizationOfQuotient p := by
  let : Algebra P S := p.toAlgebra
  let I : Ideal P := RingHom.ker p
  let hI : I ≤ RingHom.ker p := by
    intro x hx
    exact hx
  let q : (P ⧸ I) →+* S := Ideal.Quotient.lift I p hI
  have hcomp : q.comp (Ideal.Quotient.mk I) = p := by
    ext x
    exact Ideal.Quotient.lift_mk I p hI
  have hqmk (x : P) : q (Ideal.Quotient.mk I x) = p x := DFunLike.congr_fun hcomp x
  let : Algebra (P ⧸ I) S := q.toAlgebra
  have hq : IsLocalization (M.map (Ideal.Quotient.mk I)) S := by
    rw [isLocalization_iff]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩⟩
      change IsUnit (q (Ideal.Quotient.mk I u))
      rw [hqmk]
      exact IsLocalization.map_units S ⟨u, hu⟩
    constructor
    · intro z
      obtain ⟨⟨x, u⟩, hz⟩ := IsLocalization.surj M z
      refine ⟨⟨Ideal.Quotient.mk I x, ⟨Ideal.Quotient.mk I (u : P), ?_⟩⟩, ?_⟩
      · exact Submonoid.mem_map.mpr ⟨(u : P), u.2, rfl⟩
      change z * q (Ideal.Quotient.mk I (u : P)) = q (Ideal.Quotient.mk I x)
      rw [hqmk, hqmk]
      exact hz
    · intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change q (Ideal.Quotient.mk I x) = q (Ideal.Quotient.mk I y) at hxy
      obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := M) (S := S)
        (show p x = p y from by simpa only [hqmk] using hxy)
      refine ⟨⟨Ideal.Quotient.mk I (u : P),
        Submonoid.mem_map.mpr ⟨(u : P), u.2, rfl⟩⟩, ?_⟩
      simpa only [map_mul] using congrArg (Ideal.Quotient.mk I) hu
  exact ⟨I, M.map (Ideal.Quotient.mk I), q, hcomp, hq⟩

private theorem isLocalizationOfQuotient_of_surjective
    {P A S : Type*} [CommRing P] [CommRing A] [CommRing S]
    (a : P →+* A) (ha : Function.Surjective a) (b : A →+* S) (M : Submonoid A)
    (hloc : letI : Algebra A S := b.toAlgebra; IsLocalization M S) :
    RingHom.IsLocalizationOfQuotient (b.comp a) := by
  let : Algebra A S := b.toAlgebra
  let I : Ideal P := RingHom.ker a
  let e : (P ⧸ I) ≃+* A := RingHom.quotientKerEquivOfSurjective ha
  let q : (P ⧸ I) →+* S := (algebraMap A S).comp e.toRingHom
  have hcomp : q.comp (Ideal.Quotient.mk I) = b.comp a := by
    ext x
    change b (e (Ideal.Quotient.mk I x)) = b (a x)
    change b ((RingHom.quotientKerEquivOfSurjective ha) (Ideal.Quotient.mk I x)) = b (a x)
    exact congrArg b (RingHom.quotientKerEquivOfSurjective_apply_mk ha x)
  let : Algebra (P ⧸ I) S := q.toAlgebra
  have hq : IsLocalization (M.map e.symm) S := by
    convert IsLocalization.isLocalization_of_base_ringEquiv M S e.symm using 1
    apply Algebra.algebra_ext
    intro x
    rfl
  exact ⟨I, M.map e.symm, q, hcomp, hq⟩

theorem essFiniteType_iff_essFiniteType_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.EssFiniteType f ↔
      RingHom.EssFiniteType ((Ideal.Quotient.mk m).comp f) := by
  algebraize [f, (Ideal.Quotient.mk m).comp f]
  let : Algebra R (S ⧸ m) := ((Ideal.Quotient.mk m).comp f).toAlgebra
  constructor
  · intro hf
    exact RingHom.EssFiniteType.comp hf
      (RingHom.FiniteType.essFiniteType
        (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective))
  · intro hq
    change Algebra.EssFiniteType R (S ⧸ m) at hq
    rw [Algebra.essFiniteType_iff_exists_subalgebra] at hq
    rcases hq with ⟨A, M, hA, hloc⟩
    obtain ⟨n, a, ha⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
    choose b hb using fun i : Fin n =>
      Ideal.Quotient.mk_surjective (a (MvPolynomial.X i)).1
    let p : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval b
    let q : S →ₐ[R] S ⧸ m :=
      { toRingHom := Ideal.Quotient.mk m
        commutes' := by
          intro r
          rfl }
    have hp : q.comp p = A.val.comp a := by
      apply MvPolynomial.algHom_ext
      intro i
      simpa [AlgHom.comp_apply, q, p] using hb i
    let I : Ideal (MvPolynomial (Fin n) R) :=
      (IsLocalRing.maximalIdeal S).comap p.toRingHom
    have hpunit (x : I.primeCompl) : IsUnit (p.toRingHom x) := by
      apply IsLocalRing.notMem_maximalIdeal.mp
      intro hx
      exact x.2 hx
    have hm : m = IsLocalRing.maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal (inferInstance : m.IsMaximal)
    let h : Localization I.primeCompl →+* S :=
      IsLocalization.lift (M := I.primeCompl) (g := p.toRingHom) hpunit
    have hcomp : h.comp (algebraMap _ _) = p.toRingHom := by
      exact IsLocalization.lift_comp hpunit
    have hqunit (x : I.primeCompl) :
        IsUnit ((Ideal.Quotient.mk m).comp p.toRingHom x) := by
      change IsUnit ((Ideal.Quotient.mk m) (p.toRingHom x))
      exact IsUnit.map (Ideal.Quotient.mk m) (hpunit x)
    let hr : Localization I.primeCompl →+* S ⧸ m :=
      IsLocalization.lift (M := I.primeCompl)
        (g := (Ideal.Quotient.mk m).comp p.toRingHom) hqunit
    have hqr : hr = (Ideal.Quotient.mk m).comp h := by
      apply IsLocalization.lift_unique hqunit
      intro x
      exact congrArg (Ideal.Quotient.mk m) (RingHom.congr_fun hcomp x)
    have hsurj : Function.Surjective hr := by
      intro z
      obtain ⟨⟨x, u⟩, hz⟩ := IsLocalization.surj M z
      obtain ⟨x', hx'⟩ := ha x
      obtain ⟨u', hu'⟩ := ha u
      have hpuq : q (p u') = algebraMap A (S ⧸ m) u := by
        have hpuq' := DFunLike.congr_fun hp u'
        change q (p u') = A.val (a u') at hpuq'
        rw [hpuq']
        rw [hu']
        rfl
      have huI : u' ∉ I := by
        intro huI
        have huI' : p.toRingHom u' ∈ IsLocalRing.maximalIdeal S := huI
        rw [← hm] at huI'
        have hz0 : q (p u') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr huI'
        have hu0 : IsUnit (0 : S ⧸ m) := by
          rw [← hz0, hpuq]
          exact hloc.map_units (S ⧸ m) u
        exact not_isUnit_zero hu0
      let v : Localization I.primeCompl :=
        IsLocalization.mk' _ x' ⟨u', show u' ∈ I.primeCompl from huI⟩
      have hv : hr v = z := by
        apply (IsLocalization.lift_mk'_spec hqunit x' z
          ⟨u', show u' ∈ I.primeCompl from huI⟩).mpr
        change q (p x') = q (p u') * z
        calc
          q (p x') = A.val (a x') := DFunLike.congr_fun hp x'
          _ = q (p u') * z := by
            rw [hx', hpuq]
            simpa [mul_comm] using hz.symm
      exact ⟨v, hv⟩
    have hhfin : RingHom.Finite h := by
      apply (finite_iff_finite_residue h m).mpr
      rw [← hqr]
      exact RingHom.Finite.of_surjective _ hsurj
    have hhloc : RingHom.EssFiniteType h :=
      RingHom.FiniteType.essFiniteType hhfin.to_finiteType
    have hP : RingHom.FiniteType (algebraMap R (MvPolynomial (Fin n) R)) := by
      rw [RingHom.finiteType_algebraMap]
      infer_instance
    have hLoc : RingHom.EssFiniteType
        ((algebraMap (MvPolynomial (Fin n) R) (Localization I.primeCompl)).comp
          (algebraMap R (MvPolynomial (Fin n) R))) :=
      RingHom.EssFiniteType.comp
        (RingHom.FiniteType.essFiniteType hP)
        (by
          rw [RingHom.essFiniteType_algebraMap]
          exact Algebra.EssFiniteType.of_isLocalization
            (R := MvPolynomial (Fin n) R) (S := Localization I.primeCompl) I.primeCompl)
    have htotal := RingHom.EssFiniteType.comp hLoc hhloc
    have hpcomp : p.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) = f := by
      ext r
      change p (algebraMap R (MvPolynomial (Fin n) R) r) = algebraMap R S r
      exact p.commutes r
    have htotal' : RingHom.EssFiniteType
        ((h.comp (algebraMap (MvPolynomial (Fin n) R) (Localization I.primeCompl))).comp
          (algebraMap R (MvPolynomial (Fin n) R))) := by
      simpa only [RingHom.comp_assoc] using htotal
    rw [hcomp, hpcomp] at htotal'
    exact htotal'

/-! ## Localization at a closed point of the special fibre -/

/- The polynomial ring is `MvPolynomial (Fin n) R`.  The maximal ideal is
   represented by `MaximalSpectrum`, which also supplies the prime instance
   needed for `Localization.AtPrime`. -/
theorem exists_localization_at_closed_point_special_fibre
    {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) (hf : RingHom.EssFiniteType f) :
    ∃ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) R)),
      m.asIdeal.comap (algebraMap R (MvPolynomial (Fin n) R)) =
          IsLocalRing.maximalIdeal R ∧
        ∃ h : Localization.AtPrime m.asIdeal →+* S,
          h.comp
              ((algebraMap (MvPolynomial (Fin n) R)
                (Localization.AtPrime m.asIdeal)).comp
                (algebraMap R (MvPolynomial (Fin n) R))) = f ∧
            RingHom.IsLocalizationOfQuotient h := by
  sorry

end Formalization.Books.Algebra.Unit54
