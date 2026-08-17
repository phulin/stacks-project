import Formalization.Books.Algebra.Unit93.CharacterizingProjectiveModules

/-!
# Commutative Algebra, Chapter 93: Ascending properties of modules

The base-change tensor product is written in Mathlib's canonical orientation
`S ⊗[R] M`.  An `Algebra R S` instance is the standard Lean representation of
the source's ring map `R → S`.
-/

namespace Formalization.Books.Algebra.Unit93

open Formalization.Books.Algebra.Unit84
open Formalization.Books.Algebra.Unit88
open scoped TensorProduct

universe u v

noncomputable section

/- The flatness clause is already the earlier, source-faithful theorem
`Formalization.Books.Algebra.Unit39.flat_base_change`; it is included in the
combined interface below rather than duplicated under a parallel name. -/

/-- All four properties in the source ascend along arbitrary ring maps. -/
theorem ascend_properties_modules
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] :
    (Module.Flat R M → Module.Flat S (S ⊗[R] M)) ∧
      (IsMittagLefflerModule (ModuleCat.of R M) →
        IsMittagLefflerModule (ModuleCat.of S (S ⊗[R] M))) ∧
        (IsDirectSumOfCountablyGeneratedModules (ModuleCat.of R M) →
          IsDirectSumOfCountablyGeneratedModules
            (ModuleCat.of S (S ⊗[R] M))) ∧
          (Module.Projective R M → Module.Projective S (S ⊗[R] M)) := by
  sorry

end

end Formalization.Books.Algebra.Unit93
