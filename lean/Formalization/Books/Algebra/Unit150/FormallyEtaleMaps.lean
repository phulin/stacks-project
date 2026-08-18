import Formalization.Books.Algebra.Unit133.FiniteOrderDifferentialOperators
import Formalization.Books.Algebra.Unit148.FormallyUnramifiedMaps
import Mathlib.Algebra.DirectSum.Ring
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
  sorry

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
  letI : Algebra R' (R' ⊗[R] S) := Algebra.TensorProduct.leftAlgebra
  letI : Algebra.FormallyEtale R S := h
  infer_instance

/-- For a ring map of finite presentation, formal étaleness is equivalent to
étaleness. -/
theorem formallyEtale_iff_etale_of_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hfp : f.FinitePresentation) :
    f.FormallyEtale ↔ f.Etale := by
  sorry

/-- A directed colimit of formally étale algebras is formally étale. -/
theorem formallyEtale_directedColimit
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (D : DirectedAlgebraColimit f)
    (h : ∀ i,
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
  simp [infinitesimalKernel]

/-- The canonical map on the infinitesimal quotients. -/
def infinitesimalQuotientMap
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S) (n : ℕ) :
    R ⧸ (infinitesimalKernel f J) ^ n →+* S ⧸ J ^ n :=
  Ideal.quotientMap (J ^ n) f (by
    refine (Ideal.map_le_iff_le_comap).mp ?_
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_comap_le (f := f) (K := J)) n)

/-- The `n`th associated-graded piece of an ideal filtration. -/
abbrev associatedGradedPiece
    (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ) :=
  (↥(I ^ n • (⊤ : Submodule R R))) ⧸
    (I • (⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R R))))

/-- The external direct sum of the associated-graded pieces. -/
abbrev associatedGraded
    (R : Type u) [CommRing R] (I : Ideal R) :=
  ⨁ n, associatedGradedPiece R I n

/-- A graded ring equivalence between two external associated-graded rings.
The component maps and the homogeneous-component equation retain the grading
that is implicit in the textbook's displayed graded-ring isomorphism. -/
structure AssociatedGradedRingEquivalence
    {R S : Type u} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) where
  sourceRing : DirectSum.GCommRing (fun n => associatedGradedPiece R I n)
  targetRing : DirectSum.GCommRing (fun n => associatedGradedPiece S J n)
  equiv :
    letI := sourceRing
    letI := targetRing
    associatedGraded R I ≃+* associatedGraded S J
  component : ∀ n, associatedGradedPiece R I n →+ associatedGradedPiece S J n
  equiv_homogeneous :
    letI := sourceRing
    letI := targetRing
    ∀ (n : ℕ) (x : associatedGradedPiece R I n),
      equiv (DirectSum.of (fun n => associatedGradedPiece R I n) n x) =
        DirectSum.of (fun n => associatedGradedPiece S J n) n (component n x)

/-- Formal étaleness identifies all infinitesimal quotients and their
associated graded rings. -/
theorem formallyEtale_lift_infinitesimal
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (J : Ideal S)
    (hquot : Function.Surjective ((Ideal.Quotient.mk J).comp f))
    (hf : f.FormallyEtale) :
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
    (formallyEtale_lift_infinitesimal f J hquot hf).1 n⟩

/-! ## Diagonal powers, differentials, and principal parts -/

/-- The diagonal-power quotient is the displayed quotient in the source's
principal-parts argument. -/
theorem formallyEtale_omega
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    (hf : Algebra.FormallyEtale S S') (k : ℕ) :
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
  letI : Algebra.FormallyEtale S S' := hf
  exact ⟨KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'⟩

/-- The module used after base change in the principal-parts lemma. -/
abbrev principalPartsBaseChangeModule
    {S S' M : Type u} [CommRing S] [CommRing S'] [AddCommGroup M]
    [Algebra S S'] [Module S M] := S' ⊗[S] M

/-- Base change of every module of principal parts along a formally étale map. -/
theorem formallyEtale_principalParts
    {R S S' M : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (hf : Algebra.FormallyEtale S S') (k : ℕ) :
    letI : Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M) :=
      TensorProduct.leftModule
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
    M →ₗ[S] principalPartsBaseChangeModule (S := S) (S' := S') M :=
  TensorProduct.AlgebraTensorModule.mk S S' S M 1

/-- Every finite-order differential operator has a unique extension to the
scalar-extended modules, of the same (hence no greater) order. -/
theorem formallyEtale_differentialOperator_extension
    {R S S' M N : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module S N] [Module R M] [Module R N]
    [IsScalarTower R S M] [IsScalarTower R S N]
    [Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    [Module R (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [Module R (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    [IsScalarTower R S'
      (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [IsScalarTower R S'
      (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    (hf : Algebra.FormallyEtale S S') (k : ℕ)
    (D : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k) :
    ∃! E : DifferentialOperator (R := R) (S := S')
        (M := principalPartsBaseChangeModule (S := S) (S' := S') M)
        (N := principalPartsBaseChangeModule (S := S) (S' := S') N) k,
      E.1.comp
          (principalPartsBaseChangeMap (S := S) (S' := S') (M := M)).restrictScalars R =
        (principalPartsBaseChangeMap (S := S) (S' := S') (M := N)).restrictScalars R |>.comp D.1 := by
  sorry

/-- Extensions of two finite-order differential operators compose to the
extension of their composite. -/
theorem formallyEtale_differentialOperator_comp_extension
    {R S S' M N L : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
    [Module S M] [Module S N] [Module S L]
    [Module R M] [Module R N] [Module R L]
    [IsScalarTower R S M] [IsScalarTower R S N] [IsScalarTower R S L]
    [Module S' (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [Module S' (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    [Module S' (principalPartsBaseChangeModule (S := S) (S' := S') L)]
    [Module R (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [Module R (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    [Module R (principalPartsBaseChangeModule (S := S) (S' := S') L)]
    [IsScalarTower R S'
      (principalPartsBaseChangeModule (S := S) (S' := S') M)]
    [IsScalarTower R S'
      (principalPartsBaseChangeModule (S := S) (S' := S') N)]
    [IsScalarTower R S'
      (principalPartsBaseChangeModule (S := S) (S' := S') L)]
    (hf : Algebra.FormallyEtale S S') (k₁ k₂ : ℕ)
    (D₁ : DifferentialOperator (R := R) (S := S) (M := M) (N := N) k₁)
    (D₂ : DifferentialOperator (R := R) (S := S) (M := N) (N := L) k₂)
    (E₁ : DifferentialOperator (R := R) (S := S')
      (M := principalPartsBaseChangeModule (S := S) (S' := S') M)
      (N := principalPartsBaseChangeModule (S := S) (S' := S') N) k₁)
    (E₂ : DifferentialOperator (R := R) (S := S')
      (M := principalPartsBaseChangeModule (S := S) (S' := S') N)
      (N := principalPartsBaseChangeModule (S := S) (S' := S') L) k₂)
    (h₁ : E₁.1.comp
      (principalPartsBaseChangeMap (S := S) (S' := S') (M := M)).restrictScalars R =
        (principalPartsBaseChangeMap (S := S) (S' := S') (M := N)).restrictScalars R |>.comp D₁.1)
    (h₂ : E₂.1.comp
      (principalPartsBaseChangeMap (S := S) (S' := S') (M := N)).restrictScalars R =
        (principalPartsBaseChangeMap (S := S) (S' := S') (M := L)).restrictScalars R |>.comp D₂.1) :
    (differentialOperatorComp E₂ E₁).1.comp
        (principalPartsBaseChangeMap (S := S) (S' := S') (M := M)).restrictScalars R =
      (principalPartsBaseChangeMap (S := S) (S' := S') (M := L)).restrictScalars R |>.comp
        (D₂.1.comp D₁.1) := by
  sorry

/- The source's final module-action sentence is accounted for by the preceding
composition theorem together with `differentialOperatorComp`: the earlier
chapter deliberately represents finite-order operators as the filtered
submodules `DifferentialOperator`, rather than introducing a second
all-orders differential-operator algebra here. -/

end

end Formalization.Books.Algebra.Unit150
