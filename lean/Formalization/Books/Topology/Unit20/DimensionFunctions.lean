import Formalization.Books.Topology.Unit09.NoetherianSpaces
import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.Topology.Inseparable
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sober

/-!
# Topology, Chapter 20: Dimension functions

The source's specialization relation is Mathlib's `Specializes`.  The
dimension-function predicate below is new source-specific infrastructure;
immediate specializations are represented by the corresponding cover
relation in the specialization preorder.  Relative codimension uses the
canonical `relativeCodimension` from Chapter 11.
-/

namespace Formalization.Books.Topology.Unit20

open Set Function _root_.Topology TopologicalSpace
open Formalization.Books.Topology.Unit08
open Formalization.Books.Topology.Unit09
open Formalization.Books.Topology.Unit11

universe u

section DimensionFunctions

variable {X : Type u} [TopologicalSpace X]

/-! ## Definitions -/

/-
The source warns that this terminology is nonstandard and is usually used
for (locally) Noetherian schemes, where strict decrease along every
nontrivial specialization follows from the immediate-specialization
condition.  We retain both conditions because the source defines the notion
for arbitrary topological spaces.
-/

/-- `y` is an immediate specialization of `x`. -/
def IsImmediateSpecialization (x y : X) : Prop :=
  x ≠ y ∧ x ⤳ y ∧
    ¬ ∃ z : X, z ≠ x ∧ z ≠ y ∧ x ⤳ z ∧ z ⤳ y

/--
A dimension function decreases strictly along nontrivial specializations and
decreases by exactly one along immediate specializations.
-/
def IsDimensionFunction (δ : X → ℤ) : Prop :=
  (∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ x > δ y) ∧
    (∀ ⦃x y : X⦄, IsImmediateSpecialization x y → δ x = δ y + 1)

/-!
The following bridge exposes the ambient-subspace order needed to express
the source's `codim(closure {y}, closure {x})` using Chapter 11's canonical
relative codimension.
-/

theorem closureSingletonIrreducibleClosed_le_of_specializes
    {x y : X} (hxy : x ⤳ y) :
    closureSingletonIrreducibleClosed y ≤
      closureSingletonIrreducibleClosed x := by
  change closure ({y} : Set X) ⊆ closure ({x} : Set X)
  exact hxy.closure_subset

/-! ## Basic consequences -/

/-- Adding an integer constant to a dimension function gives another one. -/
theorem isDimensionFunction_add_const
    (δ : X → ℤ) (hδ : IsDimensionFunction δ) (t : ℤ) :
    IsDimensionFunction (fun x => δ x + t) := by
  sorry

/-! ## Catenarity and codimension -/

/-
The source cautions that dimension functions are most natural on sober
spaces.  Sobriety is represented by the established `[QuasiSober X]`
`[T0Space X]` assumptions on the results below; no parallel soberification
construction is introduced here.
-/

/--
A sober space carrying a dimension function is catenary, and the difference
of the function along a specialization is its relative codimension.

The codimension is `ℕ∞`, while the dimension difference is an integer.  The
well-typed form below records the source identity through `Int.toNat`; the
dimension-function hypotheses imply that this difference is nonnegative.
-/
theorem isCatenary_of_isDimensionFunction
    [QuasiSober X] [T0Space X]
    (δ : X → ℤ) (hδ : IsDimensionFunction δ) :
    IsCatenary X ∧
      ∀ ⦃x y : X⦄ (hxy : x ⤳ y),
        0 ≤ δ x - δ y ∧
          relativeCodimension
              (closureSingletonIrreducibleClosed_le_of_specializes hxy) =
            (δ x - δ y).toNat := by
  sorry

/-! ## Uniqueness -/

/-- Two dimension functions differ by a locally constant integer-valued map. -/
theorem isLocallyConstant_sub_of_isDimensionFunction
    [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X]
    (δ δ' : X → ℤ)
    (hδ : IsDimensionFunction δ) (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (fun x => δ x - δ' x) := by
  sorry

/-! ## Local existence -/

/--
In a locally Noetherian, sober, catenary space every point has an open
neighbourhood carrying a dimension function.
-/
theorem exists_open_isDimensionFunction_nhds
    [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X]
    (hX : IsCatenary X) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ δ : U → ℤ, IsDimensionFunction δ := by
  sorry

/-!
The final source remark identifies the obstruction with a class in
`H^1(X, ℤ)`.  This chapter has no canonical topological/sheaf-cohomology API
or definition of that obstruction, so the remark is retained here as
documentation rather than replaced by an unrelated formal predicate.
-/

end DimensionFunctions

end Formalization.Books.Topology.Unit20
