import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Finiteness.NilpotentKer
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
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

theorem essFinitePresentation_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange @RingHom.EssFinitePresentation := by
  apply RingHom.IsStableUnderBaseChange.mk essFinitePresentation_respectsIso
  intros R S T _ _ _ _ _ h
  change essFinitePresentation R T at h
  rcases h with ⟨A, hA, g, M, q, hq, hcomp, hloc⟩
  let : CommRing A := hA
  letI : Algebra R A := g.toAlgebra
  letI : Algebra A T := q.toAlgebra
  let : IsScalarTower R A T := IsScalarTower.of_algebraMap_eq' (by
    rw [← hcomp]
    rfl)
  let qₐ : A →ₐ[R] T := IsScalarTower.toAlgHom R A T
  let q' : (S ⊗[R] A) →+* (S ⊗[R] T) :=
    (Algebra.TensorProduct.map (AlgHom.id S S) qₐ).toRingHom
  letI : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra A (S ⊗[R] T) :=
    (Algebra.TensorProduct.includeRight.comp qₐ).toRingHom.toAlgebra
  letI : Algebra (S ⊗[R] A) (S ⊗[R] T) := q'.toAlgebra
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
  simpa [q', RingHom.algebraMap_toAlgebra] using
    congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_comp_includeLeft (AlgHom.id S S) qₐ)

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
    choose b hb using fun i : Fin n => Ideal.Quotient.mk_surjective (a (MvPolynomial.X i))
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

theorem essFiniteType_iff_essFiniteType_residue
    {R S : Type*} [CommRing R] [CommRing S]
    [IsArtinianRing S] [IsLocalRing S]
    (f : R →+* S) (m : Ideal S) [m.IsMaximal] :
    RingHom.EssFiniteType f ↔
      RingHom.EssFiniteType ((Ideal.Quotient.mk m).comp f) := by
  sorry

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
