import Formalization.Books.StacksPerfect.Unit01.Core

/-!
# Derived Categories of Stacks, Chapter 1: the lisse-étale and flat-fppf sites

This file formalizes the three lemmas in the source section.  Equalities of
functors and derived objects are represented by natural isomorphisms or
categorical isomorphisms, as required by the categorical API.

The source warns that the derived shriek functor for modules is not known
beforehand to agree with the derived shriek functor for abelian sheaves.  The
two coefficient cases below are consequently kept separate; no unwarranted
agreement is asserted.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Formalization.Books.StacksMorphisms.Unit07

universe u

namespace Formalization.Books.StacksPerfect.Unit01

variable {𝒮 : Type u} [Category.{u} 𝒮]
  [AlgebraicStackCategory 𝒮]

/-! The earlier stack-morphism interface does not expose smoothness.  This
small explicit interface supplies the missing predicate needed by the
functoriality statement; flatness is already available as `Flat`. -/
structure StackSmoothnessData (𝒮 : Type u) [Category.{u} 𝒮]
    [AlgebraicStackCategory 𝒮] where
  isSmooth : ∀ {X Y : 𝒮}, (X ⟶ Y) → Prop

def IsSmoothStackMorphism {𝒮 : Type u} [Category.{u} 𝒮]
    [AlgebraicStackCategory 𝒮] (D : StackSmoothnessData 𝒮)
    {X Y : 𝒮} (f : X ⟶ Y) : Prop :=
  D.isSmooth f

def IsApplicableForComparison {𝒮 : Type u} [Category.{u} 𝒮]
    [AlgebraicStackCategory 𝒮] (D : StackSmoothnessData 𝒮)
    {X Y : 𝒮} (f : X ⟶ Y) : ComparisonKind → Prop
  | .lisseEtale => IsSmoothStackMorphism D f
  | .flatFppf => Flat f

/-! ## Lemma 1: derived shriek -/

/-- The four cases of the source lemma: two coefficient categories for each
of the lisse-étale and flat-fppf comparisons.  The existence statement is
kept as one indexed theorem so that the four interfaces cannot drift apart. -/
theorem lemma_shriek_derived (X : 𝒮) [StackSiteData X] [SiteComparisonData X] :
    ∀ c : ComparisonKind, ∀ κ : CoefficientKind,
      Nonempty (DerivedComparisonStatement X c κ) := by
  sorry

/-- A chosen derived comparison supplied by `lemma_shriek_derived`. -/
noncomputable def selectedDerivedComparison (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] (c : ComparisonKind) (κ : CoefficientKind) :
    DerivedComparisonStatement X c κ :=
  Classical.choice (lemma_shriek_derived X c κ)

/-- The selected left derived functor `Lg_!`. -/
noncomputable def derivedShriek (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] (c : ComparisonKind) (κ : CoefficientKind) :
    SiteDerivedCategory X (fineSite c) κ ⥤ SiteDerivedCategory X (coarseSite c) κ :=
  (selectedDerivedComparison X c κ).leftDerived.functor

/-- The adjunction `Lg_! ⊣ g^*` in each coefficient case. -/
noncomputable def derivedShriekAdjunction (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] (c : ComparisonKind) (κ : CoefficientKind) :
    derivedShriek X c κ ⊣ derivedInverseImage X c κ :=
  (selectedDerivedComparison X c κ).adjunction

/-- The natural isomorphism expressing `g^* Lg_! = id`. -/
noncomputable def derivedInverseImageShriekIso (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] (c : ComparisonKind) (κ : CoefficientKind) :
    𝟭 (SiteDerivedCategory X (fineSite c) κ) ≅
      derivedShriek X c κ ⋙ derivedInverseImage X c κ :=
  (selectedDerivedComparison X c κ).unitIso

/-- The underived shriek functor in the source notation. -/
def shriek (X : 𝒮) [StackSiteData X] [SiteComparisonData X]
    (c : ComparisonKind) (κ : CoefficientKind) :
    CoefficientCarrier X (fineSite c) κ ⥤ CoefficientCarrier X (coarseSite c) κ :=
  SiteComparisonData.shriek (X := X) c κ

/-- The underived inverse-image functor in the source notation. -/
def inverseImage (X : 𝒮) [StackSiteData X] [SiteComparisonData X]
    (c : ComparisonKind) (κ : CoefficientKind) :
    CoefficientCarrier X (coarseSite c) κ ⥤ CoefficientCarrier X (fineSite c) κ :=
  SiteComparisonData.inverseImage (X := X) c κ

/-! ## Lemma 2: functoriality -/

variable {X Y : 𝒮} [StackSiteData X] [StackSiteData Y]
  [SiteComparisonData X] [SiteComparisonData Y]

/-- Functoriality of derived shriek and inverse image, for both coefficients
and both site comparisons.  The two underived base-change isomorphisms are
the input supplied by the preceding cohomology comparison.  The all-complexes
statement then subsumes the source's bounded, bounded-above, and arbitrary-
complex restrictions. -/
theorem lemma_lisse_etale_functorial_derived
    (S : FunctorialDerivedSquare X Y) (D : StackSmoothnessData 𝒮)
    (c : ComparisonKind) (hc : IsApplicableForComparison D S.f c)
    (hpush : ∀ κ : CoefficientKind,
      Nonempty (S.coarsePushforward c κ ⋙ inverseImage Y c κ ≅
        inverseImage X c κ ⋙ S.finePushforward c κ))
    (hshriek : ∀ κ : CoefficientKind,
      Nonempty (S.finePullback c κ ⋙ shriek X c κ ≅
        shriek Y c κ ⋙ S.coarsePullback c κ)) :
    ∀ κ : CoefficientKind,
      Nonempty ((S.coarsePushforwardData c κ).functor ⋙ derivedInverseImage Y c κ ≅
        derivedInverseImage X c κ ⋙ (S.finePushforwardData c κ).functor) ∧
      Nonempty ((S.finePullbackData c κ).functor ⋙ derivedShriek X c κ ≅
        derivedShriek Y c κ ⋙ (S.coarsePullbackData c κ).functor) := by
  sorry

/-- The first natural isomorphism in the functoriality lemma, written in the
direction of the source identity
`g^{-1} Rf_* = Rf'_* (g')^{-1}`. -/
def FunctorialDerivedPushforwardIso
    (S : FunctorialDerivedSquare X Y) (D : StackSmoothnessData 𝒮)
    (c : ComparisonKind) (hc : IsApplicableForComparison D S.f c)
    (hpush : ∀ κ : CoefficientKind,
      Nonempty (S.coarsePushforward c κ ⋙ inverseImage Y c κ ≅
        inverseImage X c κ ⋙ S.finePushforward c κ))
    (hshriek : ∀ κ : CoefficientKind,
      Nonempty (S.finePullback c κ ⋙ shriek X c κ ≅
        shriek Y c κ ⋙ S.coarsePullback c κ))
    (κ : CoefficientKind) :
    (S.coarsePushforwardData c κ).functor ⋙ derivedInverseImage Y c κ ≅
      derivedInverseImage X c κ ⋙ (S.finePushforwardData c κ).functor :=
  Classical.choice
    (lemma_lisse_etale_functorial_derived S D c hc hpush hshriek κ).1

/-- The second natural isomorphism in the functoriality lemma, written in the
direction of the source identity
`L(g')_! (f')^{-1} = f^{-1} Lg_!`. -/
def FunctorialDerivedShriekIso
    (S : FunctorialDerivedSquare X Y) (D : StackSmoothnessData 𝒮)
    (c : ComparisonKind) (hc : IsApplicableForComparison D S.f c)
    (hpush : ∀ κ : CoefficientKind,
      Nonempty (S.coarsePushforward c κ ⋙ inverseImage Y c κ ≅
        inverseImage X c κ ⋙ S.finePushforward c κ))
    (hshriek : ∀ κ : CoefficientKind,
      Nonempty (S.finePullback c κ ⋙ shriek X c κ ≅
        shriek Y c κ ⋙ S.coarsePullback c κ))
    (κ : CoefficientKind) :
    (S.finePullbackData c κ).functor ⋙ derivedShriek X c κ ≅
      derivedShriek Y c κ ⋙ (S.coarsePullbackData c κ).functor :=
  Classical.choice
    (lemma_lisse_etale_functorial_derived S D c hc hpush hshriek κ).2

/-! ## Lemma 3: higher shriek of quasi-coherent modules -/

/-- Apply the derived shriek functor to a module in degree zero. -/
noncomputable def derivedShriekOfModule (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] (c : ComparisonKind)
    (H : SiteModules X (fineSite c)) :
    SiteDerivedCategory X (coarseSite c) .module :=
  (derivedShriek X c .module).obj
    ((DerivedCategory.singleFunctor
      (CoefficientCarrier X (fineSite c) .module) 0).obj H)

/-- For a quasi-coherent module on either flat site, every cohomology module
of its derived shriek is locally quasi-coherent with flat base change. -/
theorem lemma_higher_shriek_quasi_coherent (X : 𝒮) [StackSiteData X]
    [SiteComparisonData X] :
    ∀ c : ComparisonKind,
      ∀ H : SiteModules X (fineSite c),
        IsQuasiCoherent (X := X) (fineSite c) H →
          ∀ p : ℤ,
            IsLQCohFbc (X := X) (coarseSite c)
              ((DerivedCategory.homologyFunctor
                (CoefficientCarrier X (coarseSite c) .module) p).obj
                (derivedShriekOfModule X c H)) := by
  sorry

end Formalization.Books.StacksPerfect.Unit01
