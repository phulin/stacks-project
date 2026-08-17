import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Exercises, Chapter 4: Tensor product

This file records the source-facing properties of functors between module
categories.  The exactness predicates use Mathlib's finite-limit and
finite-colimit preservation classes; the two bridge lemmas below identify
those canonical classes with the short-exact-sequence formulations in the
source.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ShortComplex

namespace Formalization.Books.Exercises.Unit04

/-! ## The functor properties used in the chapter -/

/-- The source's phrase “`R`-linear” means that every hom-map is a bundled
`R`-linear map.  Mathlib exposes its additive and scalar-preserving parts as
the separate `Functor.Additive` and `Functor.Linear` classes. -/
def IsRLinearFunctor
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) : Prop :=
  F.Additive ∧ Functor.Linear R F

/-- The canonical comparison map from the direct sum of the values of `F` to
the value of `F` on a direct sum. -/
def CommutesWithDirectSums
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) : Prop :=
  ∀ (ι : Type u) (M : ι → ModuleCat.{u} R),
    IsIso (sigmaComparison F M)

/-! The following two equivalences account exactly for the short exact
sequence definitions of right and left exactness in the source. -/

/-- Right exactness on short exact sequences is finite-colimit preservation. -/
theorem preservesFiniteColimits_iff_shortExact_map
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] :
    PreservesFiniteColimits F ↔
      ∀ (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact →
        (S.map F).Exact ∧ Epi (F.map S.g) :=
  CategoryTheory.Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F

/-- Left exactness on short exact sequences is finite-limit preservation. -/
theorem preservesFiniteLimits_iff_shortExact_map
    {R : Type u} [CommRing R]
    (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive] :
    PreservesFiniteLimits F ↔
      ∀ (S : ShortComplex (ModuleCat.{u} R)), S.ShortExact →
        (S.map F).Exact ∧ Mono (F.map S.f) :=
  CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F

end Formalization.Books.Exercises.Unit04
