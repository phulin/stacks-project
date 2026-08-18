import Formalization.Books.Duality.Unit01.CompactSupportDuality

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure LichtenbaumData {U X : Scheme.{u}} (j : U ⟶ X) where
  coherent : DerivedObject U
  cohomology : DerivedObject X
  comparison : Isomorphic cohomology (CompactlySupportedCohomology j coherent)

theorem lemma_lichtenbaum {U X : Scheme.{u}} (j : U ⟶ X)
    (K : DerivedObject U) (hcoherent : IsCoherent K) :
    Nonempty (LichtenbaumData j) := by
  sorry

theorem theorem_lichtenbaum {U X : Scheme.{u}} (j : U ⟶ X)
    (d : LichtenbaumData j) :
    Isomorphic d.cohomology (CompactlySupportedCohomology j d.coherent) := by
  exact d.comparison

end

end Formalization.Books.Duality.Unit01
