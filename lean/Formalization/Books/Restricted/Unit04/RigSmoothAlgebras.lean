import Formalization.Books.Restricted.Unit03.NaiveCotangentComplex
import Formalization.Books.MoreAlgebra.Unit85.TwoTermComplexes
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Algebraization of Formal Spaces, Chapter 4: Rig-smooth algebras

This file formalizes the definition and the three results in the source
section `Rig-smooth algebras`.  The completed naive cotangent complex is
formed from the presentation-independent two-term complex supplied by
Chapter 3 and the derived Ext predicates from More on Algebra, Chapter 85.
-/

namespace Formalization.Books.Restricted.Unit04

open CategoryTheory
open Formalization.Books.Restricted.Unit02
open Formalization.Books.Restricted.Unit03
open Formalization.Books.MoreAlgebra.Unit53
open Formalization.Books.MoreAlgebra.Unit85
open Formalization.Books.MoreAlgebra.Unit59

noncomputable section

universe u w

/-! ## The completed naive cotangent complex -/

/-- A complete algebra admits a completed polynomial presentation.

This is the presentation theorem from the preceding chapter, repackaged at
the point where Chapter 4 needs to choose one presentation. -/
theorem exists_naiveCotangentPresentation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    Nonempty (NaiveCotangentPresentation A I B) := by
  sorry

/-- A chosen completed polynomial presentation of a complete algebra. -/
noncomputable def canonicalNaiveCotangentPresentation
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    NaiveCotangentPresentation A I B :=
  Classical.choice (exists_naiveCotangentPresentation I B)

/-- The two-term complex with the source's `J/J²` in degree `-1` and
`⊕ B d xᵢ` in degree `0`.  All other terms are zero. -/
noncomputable def completedNaiveCotangentComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) :
    Formalization.Books.MoreAlgebra.Unit85.Comp B.obj := by
  classical
  let X : ℤ → ModuleCat B.obj := fun i =>
    if i = -1 then ModuleCat.of B.obj P.extension.Cotangent
    else if i = 0 then ModuleCat.of B.obj P.extension.CotangentSpace
    else ModuleCat.of B.obj (Fin 0 → B.obj)
  let d : ∀ i : ℤ, X i ⟶ X (i + 1) := fun i =>
    if hi : i = -1 then by
      subst i
      simpa [X] using ModuleCat.ofHom (NaiveCotangentDifferential P)
    else 0
  exact CochainComplex.of X d (by
    intro i
    by_cases hi : i = -1
    · subst i
      simp [d, X]
    · simp [d, hi])

/-- The derived object represented by the completed naive cotangent complex. -/
noncomputable def completedNaiveCotangentObject
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) :
    Formalization.Books.MoreAlgebra.Unit85.D B.obj :=
  (Formalization.Books.MoreAlgebra.Unit59.derivedComplexQuotient B.obj).obj
    (completedNaiveCotangentComplex P)

/-- The canonical derived naive cotangent object used in the definition of
rig-smoothness. -/
noncomputable def canonicalNaiveCotangentObject
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) :
    Formalization.Books.MoreAlgebra.Unit85.D B.obj :=
  completedNaiveCotangentObject (canonicalNaiveCotangentPresentation I B)

/-! ## Definition and the six Ext criteria -/

/-- Rig-smoothness of a complete algebra over a Noetherian adic base. -/
def RigSmooth
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) : Prop :=
  ∃ c : ℕ,
    ExtOneAnnihilatedByIdeal
      ((cprimeIdeal I B.obj) ^ c)
      (canonicalNaiveCotangentObject I B)

/-- The six equivalent formulations of power-annihilation of Ext¹ for the
completed naive cotangent object. -/
def RigSmoothExtPowerCriterion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I) : Prop :=
  List.TFAE [
    ∃ c : ℕ, ExtOneAnnihilatedByIdeal
      ((cprimeIdeal I B.obj) ^ c) (canonicalNaiveCotangentObject I B),
    ∃ c : ℕ,
      IdealAnnihilatesModule ((cprimeIdeal I B.obj) ^ c)
          (M := (HMinusOne B.obj
            (canonicalNaiveCotangentObject I B) : Type u)) ∧
        IsIPowerProjective ((cprimeIdeal I B.obj) ^ c)
          (HZero B.obj (canonicalNaiveCotangentObject I B)),
    ∃ c : ℕ, ExtOneAnnihilatedByIdealOnFiniteModules
      ((cprimeIdeal I B.obj) ^ c) (canonicalNaiveCotangentObject I B),
    IsIPowerTorsion (cprimeIdeal I B.obj)
          (HMinusOne B.obj (canonicalNaiveCotangentObject I B) : Type u) ∧
      HasProjectiveLocalizationCover (cprimeIdeal I B.obj)
          (HZero B.obj (canonicalNaiveCotangentObject I B)),
    IsIPowerTorsion (cprimeIdeal I B.obj)
          (HMinusOne B.obj (canonicalNaiveCotangentObject I B) : Type u) ∧
      HasProjectiveLocalizationCoverInIdeal (cprimeIdeal I B.obj)
          (HZero B.obj (canonicalNaiveCotangentObject I B)),
    IsIPowerTorsion (cprimeIdeal I B.obj)
          (HMinusOne B.obj (canonicalNaiveCotangentObject I B) : Type u) ∧
      EveryProjectiveLocalizationCoverInIdeal (cprimeIdeal I B.obj)
          (HZero B.obj (canonicalNaiveCotangentObject I B))]

/-- The factorization condition on a chosen completed presentation. -/
def RigSmoothFactorizationCriterion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) : Prop :=
  ∃ c : ℕ, ∀ a : A, a ∈ I ^ c →
    ∃ h : NaiveCotangentSpace P →ₗ[B.obj] NaiveCotangentConormal P,
      h.comp (NaiveCotangentDifferential P) =
        (algebraMap A B.obj a) • LinearMap.id

/-- The determinant of a Jacobian minor, with the partial derivative family
made explicit because the completed-polynomial API has no canonical
derivative operation. -/
def completedJacobianMinor
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B)
    (partialDerivative : Fin P.variableCount → P.relations → B.obj)
    {m : ℕ} (f : Fin m → P.relations) (T : Fin m → Fin P.variableCount) : B.obj :=
  Matrix.det (fun i j => partialDerivative (T i) (f j))

/-- The class of a relation in `J/J²`. -/
def completedRelationClass
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) (f : P.relations) :
    NaiveCotangentConormal P :=
  Algebra.Extension.Cotangent.mk
    ⟨f.1, by
      change f.1 ∈ RingHom.ker P.presentation
      rw [← P.relations_eq_kernel]
      exact f.2⟩

/-- The submodule generated by a finite family of relation classes. -/
def completedRelationSubmodule
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B) {m : ℕ}
    (f : Fin m → P.relations) : Submodule B.obj (NaiveCotangentConormal P) :=
  Submodule.span B.obj (Set.range (fun j => completedRelationClass P (f j)))

/-- The Jacobian/minor formulation of Artin smoothness for a completed
presentation. -/
def RigSmoothJacobianCriterion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {B : CompleteAlgebraCategory A I}
    (P : NaiveCotangentPresentation A I B)
    (partialDerivative : Fin P.variableCount → P.relations → B.obj) : Prop :=
  ∃ s : ℕ, ∃ b : Fin s → B.obj,
    PrimeSpectrum.zeroLocus (Ideal.span (Set.range b) : Set B.obj) ⊆
      PrimeSpectrum.zeroLocus (cprimeIdeal I B.obj : Set B.obj) ∧
    ∀ l : Fin s, ∃ m : ℕ, ∃ f : Fin m → P.relations,
      ∃ T : Fin m → Fin P.variableCount, Function.Injective T ∧
        completedJacobianMinor P partialDerivative f T ∣ b l ∧
        ∀ x : NaiveCotangentConormal P,
          b l • x ∈ completedRelationSubmodule P f

/-- The source's four equivalent conditions.

The source writes the partial derivatives of the completed polynomial ring as
if they were already available.  Since the preceding chapters do not expose
that continuous-derivative API, the statement records the needed derivative
family existentially; `RigSmoothJacobianCriterion` is the reusable
presentation once that family has been supplied. -/
theorem rigSmooth_iff_artin_smooth_criteria
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : CompleteAlgebraCategory A I)
    (P : NaiveCotangentPresentation A I B) :
    ∃ partialDerivative : Fin P.variableCount → P.relations → B.obj,
      List.TFAE [
        RigSmooth I B,
        RigSmoothExtPowerCriterion I B,
        RigSmoothFactorizationCriterion P,
        RigSmoothJacobianCriterion P partialDerivative] := by
  sorry

/-! ## Finite type algebras and localization -/

/-- Smoothness of a finite-type map on the complement of `V(I)`, expressed
by smoothness after localizing at every element of `I`. -/
def SmoothOnComplement
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (I : Ideal A) : Prop :=
  ∀ a : A, a ∈ I → RingHom.Smooth (Localization.awayMap f a)

/-- The corresponding predicate after replacing `B` by `B_g`. -/
def SmoothOnComplementAfterLocalization
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (g : B) : Prop :=
  ∀ a : A, a ∈ I →
    RingHom.Smooth (Localization.awayMap (algebraMap A (Localization.Away g)) a)

/-- Membership in the translate `1 + IB`. -/
def OnePlusIdealMembership
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (g : B) : Prop :=
  ∃ x : B, x ∈ Ideal.map (algebraMap A B) I ∧ g = 1 + x

/-- Smoothness off `V(I)` implies rig-smoothness after completion. -/
theorem rigSmooth_of_smoothOnComplement
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (h : SmoothOnComplement (algebraMap A B) I) :
    RigSmooth I (completedFiniteTypeAlgebra (B := B) I) := by
  sorry

/-- Rig-smoothness of the completion produces a localization which is smooth
off `V(I)`. -/
theorem exists_smoothOnComplementAfterLocalization_of_rigSmooth
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A]
    [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A)
    (h : RigSmooth I (completedFiniteTypeAlgebra (B := B) I)) :
    ∃ g : B, OnePlusIdealMembership I g ∧
      SmoothOnComplementAfterLocalization I g := by
  sorry

/-! ## Base change -/

/-- Equality of the closed sets cut out by two ideals. -/
def SameVanishingLocus
    {R : Type u} [CommRing R] (I J : Ideal R) : Prop :=
  PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus (J : Set R)

/-- A base-change element records the map and the chosen base-change object
needed in the modding-out lemma. -/
structure RigSmoothBaseChangeElement
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₂]
    (D : AdicBaseChangeData A₁ A₂)
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    (hB₂ : Nonempty (B₂ ≅
      completeBaseChangeObject D (Ideal.fg_of_isNoetherianRing D.I₂) B₁)) where
  map : B₁.obj →+* B₂.obj
  f₁ : B₁.obj
  f₂ : B₂.obj
  f₂_eq_map : f₂ = map f₁

/-- Ext¹ annihilation survives passage to the base-changed algebra after
modding out by a chosen element. -/
theorem ext_one_annihilated_after_modding_out
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    (D : AdicBaseChangeData A₁ A₂)
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    (hB₂ : Nonempty (B₂ ≅
      completeBaseChangeObject D (Ideal.fg_of_isNoetherianRing D.I₂) B₁))
    (E : RigSmoothBaseChangeElement D hB₂)
    (hE : ExtOneAnnihilatedByIdeal (Ideal.span ({E.f₁} : Set B₁.obj))
      (canonicalNaiveCotangentObject D.I₁ B₁)) :
    ExtOneAnnihilatedByIdeal (Ideal.span ({E.f₂} : Set B₂.obj))
      (canonicalNaiveCotangentObject D.I₂ B₂) := by
  sorry

/-- Rig-smoothness is preserved by the completed base change from the source
when the two ideals define the same closed subset of the new base. -/
theorem baseChange_preserves_rigSmooth
    {A₁ A₂ : Type u} [CommRing A₁] [CommRing A₂]
    [IsNoetherianRing A₁] [IsNoetherianRing A₂]
    (D : AdicBaseChangeData A₁ A₂)
    (hV : SameVanishingLocus (Ideal.map D.map D.I₁) D.I₂)
    {B₁ : CompleteAlgebraCategory A₁ D.I₁}
    {B₂ : CompleteAlgebraCategory A₂ D.I₂}
    (hB₂ : Nonempty (B₂ ≅
      completeBaseChangeObject D (Ideal.fg_of_isNoetherianRing D.I₂) B₁))
    (hB₁ : RigSmooth D.I₁ B₁) :
    RigSmooth D.I₂ B₂ := by
  sorry

end

end Formalization.Books.Restricted.Unit04
