import Formalization.Books.StacksPerfect.Unit03.Sites

/-!
# Derived Categories of Stacks, Chapter 1: cohomology comparisons

The local cohomology assertion in the source is written with `H^p(x, K)` on
the left and a derived global-sections object on the right.  The right-hand
side has the derived type, so the source-faithful categorical statement is
recorded as an isomorphism of derived global-sections objects; this is the
small correction listed in the final report.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.StacksMorphisms.Unit07

universe u

namespace Formalization.Books.StacksPerfect.Unit01

variable {𝒮 : Type u} [Category.{u} 𝒮]

/-- The constant integer sheaf on each of the four sites is supplied by the
site data; its derived object is placed in degree zero. -/
def ConstantIntegerObject (X : 𝒮) [StackSiteData X]
  (τ : SiteKind) :
    SiteDerivedCategory X τ .abelian :=
  (DerivedCategory.singleFunctor (CoefficientCarrier X τ .abelian) 0).obj
    (StackSiteData.constantIntegerSheaf (X := X) τ)

/-! The constant-object calculation is a separate comparison result; it does
not follow merely from the unit of the derived shriek/inverse-image
adjunction. -/

class ConstantIntegerComparisonData (X : 𝒮)
    [AlgebraicStackCategory 𝒮] [StackSiteData X]
    [SiteComparisonData X] [DerivedComparisonData X] where
  iso : ∀ (c : ComparisonKind),
    (derivedShriek X c .abelian).obj
        (ConstantIntegerObject X (fineSite c)) ≅
      ConstantIntegerObject X (coarseSite c)

/-! ## The constant-integer comparison -/

/-- `Lg_! ℤ = ℤ` for either the lisse-étale or the flat-fppf comparison. -/
theorem lemma_higher_shriek_Z (X : 𝒮) [AlgebraicStackCategory 𝒮]
    [StackSiteData X]
    [SiteComparisonData X] [DerivedComparisonData X]
    [ConstantIntegerComparisonData X] :
    ∀ c : ComparisonKind,
      Nonempty ((derivedShriek X c .abelian).obj
          (ConstantIntegerObject X (fineSite c)) ≅
        ConstantIntegerObject X (coarseSite c)) := by
  intro c
  exact ⟨ConstantIntegerComparisonData.iso (X := X) c⟩

/-- Derived cohomology on the coarse site agrees with derived cohomology on
the corresponding flat site, both globally and over every object.  The
coefficient index records the source's separate abelian-sheaf and module
statements; in particular the module case is not identified with the
abelian-sheaf case by fiat. -/
theorem lemma_lisse_etale_cohomology (X : 𝒮) [AlgebraicStackCategory 𝒮]
    [StackSiteData X]
    [SiteComparisonData X] [StackCohomologyData X]
    [DerivedCohomologyComparisonData X] :
    ∀ c : ComparisonKind, ∀ κ : CoefficientKind,
      ∀ K : SiteDerivedCategory X (coarseSite c) κ,
        Nonempty ((DerivedGlobalSections X (coarseSite c) κ).obj K ≅
          (DerivedGlobalSections X (fineSite c) κ).obj
            ((derivedInverseImage X c κ).obj K)) ∧
        ∀ x : StackCohomologyData.siteObject (X := X) (fineSite c),
          Nonempty ((DerivedSectionsAt X (coarseSite c) κ
              (StackCohomologyData.coarseObject (X := X) c x)).obj K ≅
              (DerivedSectionsAt X (fineSite c) κ x).obj
              ((derivedInverseImage X c κ).obj K)) := by
  intro c κ K
  constructor
  · exact ⟨(DerivedCohomologyComparisonData.globalIso (X := X) c κ).app K⟩
  · intro x
    exact ⟨(DerivedCohomologyComparisonData.localIso (X := X) c κ x).app K⟩

/-! ## Derived global and local sections -/

/-- The global-sections comparison for one coefficient category and one site
comparison. -/
def globalSectionsComparisonIso (X : 𝒮) [AlgebraicStackCategory 𝒮]
    [StackSiteData X]
    [SiteComparisonData X] [StackCohomologyData X]
    [DerivedCohomologyComparisonData X]
    (c : ComparisonKind) (κ : CoefficientKind)
    (K : SiteDerivedCategory X (coarseSite c) κ) :
    (DerivedGlobalSections X (coarseSite c) κ).obj K ≅
      (DerivedGlobalSections X (fineSite c) κ).obj
        ((derivedInverseImage X c κ).obj K) :=
  Classical.choice (lemma_lisse_etale_cohomology X c κ K).1

/-- The local-sections comparison for a fine-site object. -/
def localSectionsComparisonIso (X : 𝒮) [AlgebraicStackCategory 𝒮]
    [StackSiteData X]
    [SiteComparisonData X] [StackCohomologyData X]
    [DerivedCohomologyComparisonData X]
    (c : ComparisonKind) (κ : CoefficientKind)
    (K : SiteDerivedCategory X (coarseSite c) κ)
    (x : StackCohomologyData.siteObject (X := X) (fineSite c)) :
    (DerivedSectionsAt X (coarseSite c) κ
        (StackCohomologyData.coarseObject (X := X) c x)).obj K ≅
      (DerivedSectionsAt X (fineSite c) κ x).obj
        ((derivedInverseImage X c κ).obj K) :=
  Classical.choice ((lemma_lisse_etale_cohomology X c κ K).2 x)

end Formalization.Books.StacksPerfect.Unit01
