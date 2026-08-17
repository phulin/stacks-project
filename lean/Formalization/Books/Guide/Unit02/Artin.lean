import Formalization.Books.Guide.Unit02.Core

/-!
# A Guide to the Literature, Chapter 2: Artin

The source names Artin's deformation-theoretic criterion but does not state
its hypotheses or its conclusion in the excerpt.  Consequently the precise
definition of an Artin stack is formalized in `Core.lean`, while no invented
criterion theorem is added here.
-/

namespace Formalization.Books.Guide.Unit02

open CategoryTheory
open Formalization.Books.Stacks.Unit01

universe u v w

/-! ## Artin stacks -/

/-- Every Deligne--Mumford stack is an Artin stack, since an étale
presentation is smooth. -/
theorem isDeligneMumfordStack_isArtinStack
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J)
    (hX : IsDeligneMumfordStack S X) :
    IsArtinStack S X := by
  rcases hX with ⟨hdiagonal, ⟨P, hP⟩⟩
  exact ⟨hdiagonal, ⟨P, S.etaleImpliesSmooth P.map hP⟩⟩

/- The criterion claim is explicitly accounted for in the module
documentation: its formal statement is absent from the source section. -/

end Formalization.Books.Guide.Unit02
