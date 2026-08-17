import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Commutative Algebra, Chapter 4: Snake lemma

The source's diagram of abelian groups is represented by Mathlib's canonical
`ShortComplex.SnakeInput` interface.  Its first and third rows are the kernel
and cokernel rows of the vertical map, while its middle two rows carry the
exactness and endpoint hypotheses from the displayed diagram.
-/

namespace Formalization.Books.Algebra.Unit04

open CategoryTheory
open CategoryTheory.Limits

universe u

/-! ## Snake lemma -/

/-- A commutative snake-lemma diagram of abelian groups with exact rows.

The Mathlib structure records the vertical morphisms, the kernel and cokernel
universal properties, exactness of the two rows, and the epi/mono conditions
corresponding to the displayed terminal and initial zero objects.
-/
abbrev AbelianGroupSnakeInput :=
  CategoryTheory.ShortComplex.SnakeInput (AddCommGrpCat.{u})

/-- The connecting morphism in the snake-lemma sequence. -/
noncomputable def snakeConnectingMap (S : AbelianGroupSnakeInput.{u}) :
    S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.δ

/-- The canonical six-term sequence of kernels and cokernels. -/
noncomputable def snakeExactSequence (S : AbelianGroupSnakeInput.{u}) :
    ComposableArrows (AddCommGrpCat.{u}) 5 :=
  S.composableArrows

/-- The connecting morphism has the lift-and-descend property used in its
construction: compatible lifts through the two middle rows give the same
class in the target cokernel. -/
theorem snakeConnectingMap_spec (S : AbelianGroupSnakeInput.{u})
    {A : AddCommGrpCat.{u}}
    (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
    (h₂ : x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃)
    (h₁ : x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂) :
    x₃ ≫ snakeConnectingMap S = x₁ ≫ S.v₂₃.τ₁ := by
  simpa [snakeConnectingMap] using S.δ_eq x₃ x₂ x₁ h₂ h₁

/-- The six-term kernel-to-cokernel sequence is exact. -/
theorem snake_lemma (S : AbelianGroupSnakeInput.{u}) :
    (snakeExactSequence S).Exact := by
  simpa [snakeExactSequence] using S.snake_lemma

/-- If the top-left map `X ⟶ Y` is injective, then the first map in the
kernel-to-cokernel sequence is injective. -/
theorem snake_first_map_injective (S : AbelianGroupSnakeInput.{u})
    (hα : Function.Injective S.L₁.f) : Function.Injective S.L₀.f := by
  exact (AddCommGrpCat.mono_iff_injective S.L₀.f).1
    (@CategoryTheory.ShortComplex.SnakeInput.mono_L₀_f _ _ _ S
      ((AddCommGrpCat.mono_iff_injective S.L₁.f).2 hα))

/-- If the bottom-right map `V ⟶ W` is surjective, then the last map in the
kernel-to-cokernel sequence is surjective. -/
theorem snake_last_map_surjective (S : AbelianGroupSnakeInput.{u})
    (hγ : Function.Surjective S.L₂.g) : Function.Surjective S.L₃.g := by
  exact (AddCommGrpCat.epi_iff_surjective S.L₃.g).1
    (@CategoryTheory.ShortComplex.SnakeInput.epi_L₃_g _ _ _ S
      ((AddCommGrpCat.epi_iff_surjective S.L₂.g).2 hγ))

end Formalization.Books.Algebra.Unit04
