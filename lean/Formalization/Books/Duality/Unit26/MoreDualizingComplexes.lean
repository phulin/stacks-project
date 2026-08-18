import Formalization.Books.Duality.Unit25.GorensteinMorphisms

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

theorem lemma_descent_ascent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedObject Y) (hdualizing : IsDualizingComplexOn K)
    (hfaithfullyFlat : Prop) :
    IsDualizingComplexOn ((LPullback f).obj K) := by
  sorry

end

end Formalization.Books.Duality.Unit01
