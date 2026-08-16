import Formalization.Books.Perfect.Unit19.CharacterizingPseudoCoherent

/-!
# Perfect complexes, Chapter 19

This chapter formalizes “Characterizing pseudo-coherent complexes, I”.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Formalization.Books.Perfect.Unit19

/-- A pseudo-coherent object on a quasi-compact and quasi-separated scheme is
the homotopy colimit of perfect objects whose truncations approximate it. -/
theorem isPseudoCoherent_iff_homotopyColimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{v} X.Modules] [FinitenessPredicates X]
    [HasSequentialHomotopyColimits (DerivedCategory X.Modules)]
    (K : DerivedCategory X.Modules) :
    IsPseudoCoherent X K ↔
      ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (e : homotopyColimit F ≅ K),
        IsPerfectHomotopyColimitApproximation X K F e := by
  sorry

/-- Supported version of the homotopy-colimit characterization. -/
theorem isPseudoCoherent_iff_supported_homotopyColimit
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{v} X.Modules] [FinitenessPredicates X]
    [HasSequentialHomotopyColimits (DerivedCategory X.Modules)]
    (K : DerivedCategory X.Modules) {T : Set X} (hT : IsClosed T)
    (hTcompl : IsCompact Tᶜ) (hK : IsSupportedOn K T) :
    IsPseudoCoherent X K ↔
      ∃ (F : ℕ ⥤ DerivedCategory X.Modules) (e : homotopyColimit F ≅ K),
        IsSupportedPerfectHomotopyColimitApproximation X K T F e := by
  sorry

end Formalization.Books.Perfect.Unit19
