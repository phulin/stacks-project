import Formalization.Books.SpacesCohomology.Unit12.CoherentSheaves

/-!
# Dévissage of coherent sheaves

The declarations below expose the support decompositions and induction
principles used in the source section.  Quotients and subobject relations are
carried by explicit statement fields because the chapter's shared sheaf model
does not choose a particular implementation of an abelian sheaf category.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure SupportFiltrationStep (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (Z Z' : Set X) where
  G' : SheafObj X
  G : SheafObj X
  short_exact : ShortExactSheaves X
  left_identification : short_exact.F₁ = G'
  middle_identification : short_exact.F₂ = F
  right_identification : short_exact.F₃ = G
  coherent_G' : IsCoherentModule X G'
  coherent_G : IsCoherentModule X G
  support_G' : SupportContainedIn X G' Z'
  support_G : SupportContainedIn X G Z

theorem prepare_filter_support
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X) (Z Z' : Set X)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F)
    (hsupport : sheafSupport X F = Z ∪ Z') :
    Nonempty (SupportFiltrationStep X F Z Z') := by
  sorry

structure IrreducibleClosedSubspace (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] where
  subspace : ClosedSubspace X
  reduced : Prop
  irreducible : Prop

structure IrreducibleSupportInjection (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (F : SheafObj X) (Z : IrreducibleClosedSubspace X) where
  r : ℕ
  positive : 0 < r
  I : IdealSheaf Z.subspace.carrier
  nonzero : I.object ≠ zeroSheaf Z.subspace.carrier
  quasi_coherent : IsQuasiCoherent I.object
  map : SheafHom (pushforwardSheaf Z.subspace.inclusion
      (directSumSheaf Z.subspace.carrier r I.object)) F
  injective : Prop
  cokernel_support_proper : Prop

theorem prepare_filter_irreducible
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (_hX : IsNoetherian X) (_hF : IsCoherentModule X F)
    (Z : IrreducibleClosedSubspace X)
    (_hsupport : schemeTheoreticSupport F = Z.subspace) :
    Nonempty (IrreducibleSupportInjection X F Z) := by
  sorry

structure CoherentFiltration (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) where
  length : ℕ
  term : Fin (length + 1) → SheafObj X
  initial : term ⟨0, Nat.zero_lt_succ length⟩ = zeroSheaf X
  terminal : term ⟨length, Nat.lt_succ_self length⟩ = F
  coherent : ∀ j : Fin (length + 1), IsCoherentModule X (term j)
  subobject : ∀ _j : Fin length, Prop
  quotient : ∀ _j : Fin length, SheafObj X
  quotient_identification : ∀ _j : Fin length, Prop
  graded_support : ∀ j : Fin length, ∃ Z : IrreducibleClosedSubspace X,
    ∃ I : IdealSheaf Z.subspace.carrier,
      IsQuasiCoherent I.object ∧
      Nonempty (SheafIso X (quotient j)
        (pushforwardSheaf Z.subspace.inclusion I.object))

theorem coherent_filter
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (_hX : IsNoetherian X) (hF : IsCoherentModule X F) :
    Nonempty (CoherentFiltration X F) := by
  sorry

abbrev CoherentProperty (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] := SheafObj X → Prop

structure HigherRankGenericIdealReduction (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (P : CoherentProperty X) (Z : IrreducibleClosedSubspace X)
    (G : SheafObj X) (I : IdealSheaf Z.subspace.carrier) where
  G' : SheafObj Z.subspace.carrier
  quasi_coherent : IsQuasiCoherent G'
  inclusion : Nonempty (SheafHom G'
    (idealTimes Z.subspace.carrier I.object
      (pullbackSheaf Z.subspace.inclusion G)))
  cokernel_support_proper : Prop
  property : P (pushforwardSheaf Z.subspace.inclusion G')

structure InitialPropertyHypotheses (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (P : CoherentProperty X) where
  extension_closed : ∀ (E : ShortExactSheaves X),
    P E.F₁ → P E.F₃ → P E.F₂
  ideal_case : ∀ (Z : IrreducibleClosedSubspace X)
    (I : IdealSheaf Z.subspace.carrier),
    IsQuasiCoherent I.object →
    P (pushforwardSheaf Z.subspace.inclusion I.object)

theorem property_initial
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (P : CoherentProperty X)
    (hX : IsNoetherian X) (H : InitialPropertyHypotheses X P) :
    ∀ F : SheafObj X, IsCoherentModule X F → P F := by
  sorry

structure HigherRankPropertyHypotheses (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (P : CoherentProperty X) where
  extension_closed : ∀ (E : ShortExactSheaves X),
    P E.F₁ → P E.F₃ → P E.F₂
  rank_reduction : ∀ (F : SheafObj X) (r : ℕ), 0 < r →
    P (directSumSheaf X r F) → P F
  generic_ideal_case : ∀ (Z : IrreducibleClosedSubspace X),
    ∃ G : SheafObj X,
      IsCoherentModule X G ∧
        schemeTheoreticSupport G = Z.subspace ∧
        ∀ (I : IdealSheaf Z.subspace.carrier),
          I.ideal → IsQuasiCoherent I.object →
            I.object ≠ zeroSheaf Z.subspace.carrier →
              Nonempty (HigherRankGenericIdealReduction X P Z G I)

theorem property_higher_rank_cohomological
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (P : CoherentProperty X)
    (hX : IsNoetherian X) (H : HigherRankPropertyHypotheses X P) :
    ∀ F : SheafObj X, IsCoherentModule X F → P F := by
  sorry

structure HigherRankVariantHypotheses (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (P : CoherentProperty X) where
  two_of_three : ∀ (E : ShortExactSheaves X),
    (P E.F₁ ∧ P E.F₂ → P E.F₃) ∧
      (P E.F₁ ∧ P E.F₃ → P E.F₂) ∧
      (P E.F₂ ∧ P E.F₃ → P E.F₁)
  rank_reduction : ∀ (F : SheafObj X) (r : ℕ), 0 < r →
    P (directSumSheaf X r F) → P F
  irreducible_case : ∀ (Z : IrreducibleClosedSubspace X),
    ∃ G : SheafObj X,
      IsCoherentModule X G ∧
        schemeTheoreticSupport G = Z.subspace ∧ P G

theorem property_higher_rank_cohomological_variant
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (P : CoherentProperty X)
    (hX : IsNoetherian X) (H : HigherRankVariantHypotheses X P) :
    ∀ F : SheafObj X, IsCoherentModule X F → P F := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
