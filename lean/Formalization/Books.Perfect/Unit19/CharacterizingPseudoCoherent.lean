import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Perfect complexes, §19: Characterizing pseudo-coherent complexes, I

This section records the two characterizations in the source section.  The
Mathlib version used by the project has the derived category of an abelian
category, its canonical truncation functors, and sheaf stalks, but it does not
yet provide a theory of homotopy colimits of sequential diagrams or the
preceding chapters' finiteness predicates for derived objects.  The two small
interfaces below keep those notions explicit while reusing the canonical
Mathlib constructions everywhere else.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

namespace Formalization.«Books.Perfect».Unit19

/-! ### Interfaces supplied by the preceding chapters -/

/-- The two finiteness predicates on the derived category of `𝒪_X`-modules.

The preceding chapters define these notions geometrically.  They are kept as
an explicit interface here because those chapter APIs are not part of the
current Mathlib release. -/
class FinitenessPredicates (X : Scheme.{u})
    [HasDerivedCategory.{v} X.Modules] where
  pseudoCoherent : ObjectProperty (DerivedCategory X.Modules)
  perfect : ObjectProperty (DerivedCategory X.Modules)

/-- The source notion of a pseudo-coherent derived object. -/
def IsPseudoCoherent (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules]
    [FinitenessPredicates X] (K : DerivedCategory X.Modules) : Prop :=
  FinitenessPredicates.pseudoCoherent K

/-- The source notion of a perfect derived object. -/
def IsPerfect (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules]
    [FinitenessPredicates X] (K : DerivedCategory X.Modules) : Prop :=
  FinitenessPredicates.perfect K

/-- A chosen sequential homotopy-colimit cocone in a category.

This is the interface needed to write the source's `hocolim` notation.  In
particular, the chosen cocone supplies the maps from each stage to its
homotopy colimit. -/
class HasSequentialHomotopyColimits (C : Type u) [Category.{v} C] where
  cocone : ∀ F : ℕ ⥤ C, Cocone F

/-- The chosen homotopy colimit object of a sequential diagram. -/
def homotopyColimit {C : Type u} [Category.{v} C]
    [HasSequentialHomotopyColimits C] (F : ℕ ⥤ C) : C :=
  (HasSequentialHomotopyColimits.cocone F).pt

/-- The chosen homotopy-colimit cocone of a sequential diagram. -/
def homotopyColimitCocone {C : Type u} [Category.{v} C]
    [HasSequentialHomotopyColimits C] (F : ℕ ⥤ C) : Cocone F :=
  HasSequentialHomotopyColimits.cocone F

/-! ### Support and truncation -/

/-- The set of points where a sheaf of modules has a nonzero stalk. -/
def ModuleSupport {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | ¬ IsZero (M.presheaf.stalk x)}

/-- A derived object is supported on `T` when every cohomology sheaf has
support contained in `T`. -/
def IsSupportedOn {X : Scheme.{u}} [HasDerivedCategory.{v} X.Modules]
    (K : DerivedCategory X.Modules) (T : Set X) : Prop :=
  ∀ i : ℤ, ModuleSupport ((DerivedCategory.homologyFunctor X.Modules i).obj K) ⊆ T

/-!
The source truncation `τ_{≥ n}` is Mathlib's canonical `truncGE n` for the
canonical t-structure on the derived category.
-/
noncomputable def derivedTruncGE (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules]
    (n : ℤ) : DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  (DerivedCategory.TStructure.t (C := X.Modules)).truncGE n

/-- The map from the `n`-th stage of a sequential diagram to a target
identified with its chosen homotopy colimit. -/
def homotopyColimitStageMap {C : Type u} [Category.{v} C]
    [HasSequentialHomotopyColimits C] {F : ℕ ⥤ C} {K : C}
    (e : homotopyColimit F ≅ K) (n : ℕ) : F.obj n ⟶ K :=
  (homotopyColimitCocone F).ι.app n ≫ e.hom

/-! ### The source approximation interfaces -/

/-- The approximation condition in the first source lemma. -/
def IsPerfectHomotopyColimitApproximation
    (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules]
    [FinitenessPredicates X]
    [HasSequentialHomotopyColimits (DerivedCategory X.Modules)]
    (K : DerivedCategory X.Modules)
    (F : ℕ ⥤ DerivedCategory X.Modules)
    (e : homotopyColimit F ≅ K) : Prop :=
  ∀ n : ℕ,
    IsPerfect X (F.obj n) ∧
      IsIso ((derivedTruncGE X (-(n : ℤ))).map (homotopyColimitStageMap e n))

/-- The supported approximation condition in the second source lemma. -/
def IsSupportedPerfectHomotopyColimitApproximation
    (X : Scheme.{u}) [HasDerivedCategory.{v} X.Modules]
    [FinitenessPredicates X]
    [HasSequentialHomotopyColimits (DerivedCategory X.Modules)]
    (K : DerivedCategory X.Modules) (T : Set X)
    (F : ℕ ⥤ DerivedCategory X.Modules)
    (e : homotopyColimit F ≅ K) : Prop :=
  ∀ n : ℕ,
    IsPerfect X (F.obj n) ∧
      IsSupportedOn (F.obj n) T ∧
      IsIso ((derivedTruncGE X (-(n : ℤ))).map (homotopyColimitStageMap e n))

end Formalization.«Books.Perfect».Unit19
