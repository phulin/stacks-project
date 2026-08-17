import Mathlib.CategoryTheory.Limits.Types.Coequalizers
import Mathlib.Topology.Bases
import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Topology, Chapter 28: Colimits of spaces

The source describes coproducts and coequalizers concretely and then deduces
the existence of all colimits.  Mathlib's `TopCat` already provides the
canonical sigma-type coproduct, quotient topology on quotients, and the
relevant preservation instances.  This file records the source-facing basis
and quotient constructions while reusing those canonical APIs.
-/

namespace Formalization.Books.Topology.Unit28

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace
open _root_.Topology

universe u v

noncomputable section

section Coproducts

variable {ι : Type v} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The category of topological spaces has coproducts. -/
theorem topological_spaces_have_coproducts :
    HasCoproducts.{u} (TopCat.{u}) := by
  infer_instance

/-- The basis of the coproduct topology, written as open subsets of one summand
embedded in the dependent sum. -/
def coproductBasis : Set (Set (Σ i, X i)) :=
  ⋃ i : ι, (fun U : Set (X i) => (Sigma.mk i '' U : Set (Σ i, X i))) ''
    {U : Set (X i) | IsOpen U}

/-- The displayed family of summand opens is a basis for the coproduct topology. -/
theorem isTopologicalBasis_coproductBasis :
    IsTopologicalBasis (coproductBasis (X := X)) := by
  unfold coproductBasis
  apply IsTopologicalBasis.sigma
  intro i
  simpa using (isTopologicalBasis_opens :
    IsTopologicalBasis {U : Set (X i) | IsOpen U})

end Coproducts

section Coequalizers

variable {A B : TopCat.{u}} (a b : A ⟶ B)

/-- The category of topological spaces has coequalizers. -/
theorem topological_spaces_have_coequalizers :
    HasCoequalizers (TopCat.{u}) := by
  infer_instance

/-- The set-theoretic coequalizer of `a` and `b`, equipped with the quotient topology. -/
def coequalizerQuotient (a b : A ⟶ B) : TopCat.{u} :=
  letI : TopologicalSpace (Function.Coequalizer a b) :=
    TopologicalSpace.coinduced (Function.Coequalizer.mk a b) B.str
  TopCat.of (Function.Coequalizer a b)

/-- The canonical quotient map to the concrete coequalizer. -/
def coequalizerQuotientMap : B ⟶ coequalizerQuotient a b :=
  letI : TopologicalSpace (Function.Coequalizer a b) :=
    TopologicalSpace.coinduced (Function.Coequalizer.mk a b) B.str
  TopCat.ofHom ⟨Function.Coequalizer.mk a b, continuous_quot_mk⟩

/-- The canonical cofork from the quotient map. -/
def coequalizerQuotientCofork (a b : A ⟶ B) : Cofork a b :=
  Cofork.ofπ (coequalizerQuotientMap a b) (by
    apply TopCat.ext
    intro x
    change Function.Coequalizer.mk a b (a x) = Function.Coequalizer.mk a b (b x)
    exact Function.Coequalizer.condition a b x)

/-- The quotient construction is a coequalizer of the two given maps. -/
noncomputable def coequalizerQuotientCofork_isColimit :
    IsColimit (coequalizerQuotientCofork a b) := by
  sorry

/-- The concrete quotient map has the quotient-map property. -/
theorem coequalizerQuotientMap_isQuotientMap :
    IsQuotientMap (coequalizerQuotientMap a b) := by
  exact isQuotientMap_quot_mk

/-- The canonical categorical coequalizer is isomorphic to the concrete quotient. -/
noncomputable def coequalizerIsoQuotient :
    coequalizer a b ≅ coequalizerQuotient a b :=
  (coequalizerIsCoequalizer a b).coconePointUniqueUpToIso
    (coequalizerQuotientCofork_isColimit a b)

end Coequalizers

section Colimits

/-- The category of topological spaces has all colimits. -/
theorem topological_spaces_have_colimits :
    HasColimits (TopCat.{u}) := by
  infer_instance

/-- The forgetful functor from topological spaces to types preserves colimits. -/
theorem topological_space_forgetful_preserves_colimits :
    PreservesColimits (CategoryTheory.forget (TopCat.{u})) := by
  infer_instance

end Colimits

end

end Formalization.Books.Topology.Unit28
