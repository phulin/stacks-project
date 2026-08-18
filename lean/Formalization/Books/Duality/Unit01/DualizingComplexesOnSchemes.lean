import Formalization.Books.Duality.Unit01.Introduction
import Formalization.Books.Dualizing.Unit01

/-!
# Dualizing complexes on schemes

This file records the definitions and theorem interfaces in the second source
section.  The local derived-category context keeps the affine-local condition
explicit; the ring-level notion is the earlier `IsDualizingComplex`.
-/

namespace Formalization.Books.Duality.Unit01

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable [SchemeDerivedContext Scheme]

def HasAffineLocalDualizingCover (X : Scheme.{u}) (K : DerivedObject X) : Prop :=
  ∃ (_ : AlgebraicGeometry.Scheme.AffineOpenCover.{u, u} X), IsDualizingComplexOn K

def IsDualizingSchemeObject (X : Scheme.{u}) (K : DerivedObject X) : Prop :=
  IsDualizingComplexOn K

def definition_dualizing_scheme (X : Scheme.{u}) (K : DerivedObject X) : Prop :=
  IsDualizingSchemeObject X K

theorem lemma_equivalent_definitions (X : Scheme.{u}) (K : DerivedObject X) :
    IsDualizingSchemeObject X K ↔ HasAffineLocalDualizingCover X K := by
  sorry

def AffineDualityWitness {X : Scheme.{u}} (K L : DerivedObject X) : Prop :=
  Nonempty (InternalHom K L ≅ AffineInternalHom K L)

theorem lemma_affine_duality (X : Scheme.{u}) (K L : DerivedObject X)
    (hK : IsCoherent K) (hL : HasFiniteInjectiveDimension L) :
    AffineDualityWitness K L := by
  sorry

def AffineInternalHomEvaluation {X : Scheme.{u}}
    (K L M : DerivedObject X) : Prop :=
  IsIso (EvaluationMap K L M)

theorem lemma_internal_hom_evaluate_isom (X : Scheme.{u})
    (K L M : DerivedObject X) :
    ((IsCoherent K ∧ IsBoundedAbove K ∧ IsBoundedBelow L ∧
        HasFiniteInjectiveDimension L) ∨
      (IsCoherent K ∧ IsCoherent L ∧ HasFiniteTorDimension (InternalHom L M) ∧
        HasFiniteInjectiveDimension L)) →
      AffineInternalHomEvaluation K L M := by
  sorry

structure SchemeDualityData (X : Scheme.{u}) (K : DerivedObject X) where
  dual : (DerivedObject X)ᵒᵖ ⥤ DerivedObject X
  antiEquivalence : Nonempty ((DerivedObject X)ᵒᵖ ≌ DerivedObject X)
  doubleDual : ∀ L : DerivedObject X,
    Nonempty (L ≅ InternalHom (InternalHom L K) K)

theorem lemma_dualizing_schemes (X : Scheme.{u}) (K : DerivedObject X)
    (hK : IsDualizingSchemeObject X K) : Nonempty (SchemeDualityData X K) := by
  sorry

theorem lemma_dualizing_unique_schemes (X : Scheme.{u})
    (K K' : DerivedObject X)
    (hK : IsDualizingSchemeObject X K)
    (hK' : IsDualizingSchemeObject X K') :
    ∃ L : DerivedObject X, IsInvertibleObject L ∧
      Isomorphic K' (Tensor K L) := by
  sorry

theorem lemma_dimension_function_scheme (X : Scheme.{u})
    (ω : DerivedObject X) (hω : IsDualizingSchemeObject X ω) :
    IsUniversallyCatenary X ∧
      ∃ δ : SchemeDerivedContext.supportLabel X → ℤ,
        IsDimensionFunction δ := by
  sorry

def SittingInDegrees (X : Scheme.{u}) (ω F : DerivedObject X)
    (δ : SchemeDerivedContext.supportLabel X → ℤ) : Prop :=
  (∀ i : ℤ, IsCoherent (SheafExt (-i) F ω)) ∧
    (∀ (x : SchemeDerivedContext.supportLabel X) (i : ℤ),
      (i < δ x ∨ δ x + (SupportDimension F x : ℤ) < i) →
        IsZero (SheafExt (-i) F ω)) ∧
    (∀ (x : SchemeDerivedContext.supportLabel X) (i : ℤ),
      SupportDimension (SheafExt (-(i + δ x)) F ω) x ≤ i.natAbs) ∧
    (∀ x, IsLeast {i : ℕ |
        ¬ IsZero (SheafExt (-(i : ℤ) - δ x) F ω)} (Depth F x)) ∧
    (∀ (x : SchemeDerivedContext.supportLabel X) (i : ℤ),
      (∃ j : ℤ, j ≤ i ∧ InSupport (SheafExt (-j) F ω) x) ↔
        (Depth F x : ℤ) + δ x ≤ i)

theorem lemma_sitting_in_degrees (X : Scheme.{u}) (ω F : DerivedObject X)
    (δ : SchemeDerivedContext.supportLabel X → ℤ)
    (hω : IsDualizingSchemeObject X ω) (hF : IsCoherent F)
    (hδ : IsDimensionFunction δ) :
    SittingInDegrees X ω F δ := by
  sorry

end

end Formalization.Books.Duality.Unit01
