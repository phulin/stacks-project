import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Sites and Sheaves, Chapter 51: Topologies and continuous functors

The source section records that a continuous functor induces an adjoint pair
on sheaves.  Mathlib's `sheafPullbackConstruction.sheafAdjunctionContinuous`
is the canonical construction: its left adjoint is left Kan extension followed
by sheafification, and its right adjoint is precomposition with the continuous
functor.  The source suppresses the size and existence hypotheses, which are
made explicit here.
-/

namespace Formalization.Books.Sites.Unit51

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₂} [Category.{v₂} C]
variable {D : Type u₃} [Category.{v₃} D]

/-- A continuous functor induces the source's adjoint pair on sheaves.

The right adjoint is the sheaf functor induced by precomposition with `u`.
The left adjoint is the constructed sheaf pullback, i.e. left Kan extension
followed by sheafification.
-/
noncomputable def continuousFunctorSheafAdjunction
    (u : C ⥤ D) (A : Type u₁) [Category.{v₁} A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    [∀ (F : Cᵒᵖ ⥤ A), u.op.HasLeftKanExtension F]
    [HasWeakSheafify K A] :
    Functor.sheafPullbackConstruction.sheafPullback u A J K ⊣
      u.sheafPushforwardContinuous A J K :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u A J K

end Formalization.Books.Sites.Unit51
