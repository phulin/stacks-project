import Formalization.Books.SpacesCohomology.Unit01.FiniteAffines

/-!
# A weak version of Chow's lemma
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure WeakChowCover (X S : AlgebraicSpace.{u})
    (p : SpaceHom X S) [AlgebraicSpaceTheory.{u}] where
  X' : AlgebraicSpace.{u}
  cover : SpaceHom X' X
  structure_map : SpaceHom X' S
  X'_is_scheme : IsScheme X'
  H_quasi_projective : IsHQuasiProjective structure_map
  proper : IsProper cover
  surjective : IsSurjective cover
  over_S : Prop

theorem weak_chow
    (X S : AlgebraicSpace.{u}) (p : SpaceHom X S)
    [AlgebraicSpaceTheory.{u}]
    (hS : IsScheme S) (hsep : IsSeparated p) (hft : IsFiniteType p) :
    Nonempty (WeakChowCover X S p) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
