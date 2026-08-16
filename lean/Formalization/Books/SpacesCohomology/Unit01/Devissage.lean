import Formalization.Books.SpacesCohomology.Unit01.CoherentSheaves

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
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  F : SheafObj X
  G' : SheafObj X
  G : SheafObj X
  short_exact : ShortExactSheaves X
  coherent_G' : IsCoherentModule X G'
  coherent_G : IsCoherentModule X G
  support_G' : SupportContainedIn X G' (Set.range (fun x : X => x))
  support_G : SupportContainedIn X G (Set.range (fun x : X => x))
  support_decomposition : Prop

theorem prepare_filter_support
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X) (Z Z' : Set X)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F)
    (hsupport : sheafSupport X F = Z ∪ Z') :
    ∃ G' G : SheafObj X,
      IsCoherentModule X G' ∧ IsCoherentModule X G ∧
      SupportContainedIn X G' Z' ∧ SupportContainedIn X G Z := by
  sorry

structure IrreducibleClosedSubspace (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] where
  subspace : ClosedSubspace X
  reduced : Prop
  irreducible : Prop

structure IrreducibleSupportInjection (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  F : SheafObj X
  Z : IrreducibleClosedSubspace X
  r : ℕ
  positive : 0 < r
  I : IdealSheaf Z.subspace.carrier
  nonzero : Prop
  map : SheafHom (pushforwardSheaf Z.subspace.inclusion
      (directSumSheaf Z.subspace.carrier r I.object)) F
  injective : Prop
  cokernel_support_proper : Prop

theorem prepare_filter_irreducible
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F)
    (Z : IrreducibleClosedSubspace X)
    (hsupport : Prop) :
    Nonempty (IrreducibleSupportInjection X) := by
  sorry

structure CoherentFiltration (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) where
  length : ℕ
  term : Fin (length + 1) → SheafObj X
  initial : Prop
  terminal : Prop
  coherent : ∀ j : Fin (length + 1), IsCoherentModule X (term j)
  subobject : ∀ _j : Fin (length + 1), Prop
  quotient : ∀ _j : Fin (length + 1), SheafObj X
  quotient_identification : ∀ _j : Fin (length + 1), Prop
  graded_support : ∀ j : Fin (length + 1), ∃ Z : IrreducibleClosedSubspace X,
    ∃ I : IdealSheaf Z.subspace.carrier,
      Nonempty (SheafIso X (quotient j)
        (pushforwardSheaf Z.subspace.inclusion I.object))

theorem coherent_filter
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (hX : IsNoetherian X) (hF : IsCoherentModule X F) :
    Nonempty (CoherentFiltration X F) := by
  sorry

abbrev CoherentProperty (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] := SheafObj X → Prop

structure InitialPropertyHypotheses (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (P : CoherentProperty X) where
  extension_closed : ∀ (E : ShortExactSheaves X),
    P E.F₁ → P E.F₃ → P E.F₂
  ideal_case : ∀ (Z : IrreducibleClosedSubspace X)
    (I : IdealSheaf Z.subspace.carrier),
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
    ∃ G : SheafObj Z.subspace.carrier,
      IsCoherentModule Z.subspace.carrier G ∧
    ∀ (_I : IdealSheaf Z.subspace.carrier), Prop →
        ∃ G' : SheafObj Z.subspace.carrier,
          P (pushforwardSheaf Z.subspace.inclusion G')

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
  irreducible_case : ∀ (_Z : IrreducibleClosedSubspace X),
    ∃ G : SheafObj X, P G

theorem property_higher_rank_cohomological_variant
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (P : CoherentProperty X)
    (hX : IsNoetherian X) (H : HigherRankVariantHypotheses X P) :
    ∀ F : SheafObj X, IsCoherentModule X F → P F := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
