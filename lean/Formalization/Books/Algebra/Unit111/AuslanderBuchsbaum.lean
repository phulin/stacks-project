import Formalization.Books.Algebra.Unit72.Depth
import Formalization.Books.Algebra.Unit109.FiniteGlobalDimension

/-!
# Commutative Algebra, Chapter 111: Auslander--Buchsbaum

The source's depth values are represented by `Unit72.localDepth`, with values
in `ℕ∞`.  The projective dimension is Mathlib's canonical
`CategoryTheory.projectiveDimension`, whose values lie in `WithBot ℕ∞`; the
depths are therefore cast to that same ordered type in the formula below.
The finite-free resolution, short-exact-sequence depth inequalities, and
depth-drop interfaces used in the source proof are supplied by Chapters 71,
72, and 109.
-/

namespace Formalization.Books.Algebra.Unit111

open CategoryTheory
open Formalization.Books.Algebra.Unit72
open Formalization.Books.Algebra.Unit109

universe u

noncomputable section

/-! ## The Auslander--Buchsbaum formula -/

/-- **Auslander--Buchsbaum formula.**  For a nonzero finite module of finite
projective dimension over a Noetherian local ring, the depth of the ring is
the sum of the module's projective dimension and its depth. -/
theorem auslander_buchsbaum
    {R M : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hpd : HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    ((localDepth R R : ℕ∞) : WithBot ℕ∞) =
      CategoryTheory.projectiveDimension (ModuleCat.of R M) +
        ((localDepth R M : ℕ∞) : WithBot ℕ∞) := by
  sorry

end

end Formalization.Books.Algebra.Unit111
