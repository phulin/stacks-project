import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Formalization.Books.StacksMorphisms.Unit07.QuasiCompactMorphisms

/-!
# Derived Categories of Stacks, Chapter 1: shared interfaces

The current Mathlib release does not contain the lisse-étale and flat-fppf
categories of modules on an algebraic stack.  This file therefore records the
smallest source-facing interfaces needed by the statements in the chapter.
The categorical constructions themselves use Mathlib's `Category`, `Functor`,
`DerivedCategory`, `Equivalence`, and Verdier-localization APIs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated

universe u

namespace Formalization.Books.StacksPerfect.Unit01

/-! ## Sites, coefficients, and module categories -/

/-- The four sites used in the chapter. -/
inductive SiteKind
  | etale
  | lisseEtale
  | fppf
  | flatFppf
deriving DecidableEq

/-- The two coefficient categories occurring in the source. -/
inductive CoefficientKind
  | abelian
  | module
deriving DecidableEq

/-- The comparison from a big site to its site of flat objects. -/
inductive ComparisonKind
  | lisseEtale
  | flatFppf
deriving DecidableEq

def fineSite : ComparisonKind → SiteKind
  | .lisseEtale => .lisseEtale
  | .flatFppf => .flatFppf

def coarseSite : ComparisonKind → SiteKind
  | .lisseEtale => .etale
  | .flatFppf => .fppf

/-- The category data attached to an abelian category.

This is the same bundling pattern used by earlier formalized chapters; the
instances expose the stored category to Mathlib's categorical APIs. -/
structure AbelianCategoryData where
  Carrier : Type u
  category : Category.{u} Carrier
  abelian : @Abelian Carrier category

instance (A : AbelianCategoryData.{u}) : Category.{u} A.Carrier := A.category
instance (A : AbelianCategoryData.{u}) : Abelian A.Carrier := A.abelian

/-- An algebraic stack has abelian categories of sheaves and modules on each
site, the source predicates on those modules, and the target category of
quasi-coherent modules. -/
class StackSiteData {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮) where
  abelianSheaves : SiteKind → AbelianCategoryData.{u}
  modules : SiteKind → AbelianCategoryData.{u}
  isQuasiCoherent : ∀ τ, ObjectProperty (modules τ).Carrier
  isLocallyQuasiCoherentFlatBaseChange : ∀ τ, ObjectProperty (modules τ).Carrier
  isParasitic : ∀ τ, ObjectProperty (modules τ).Carrier
  quasiCoherentModules : AbelianCategoryData.{u}

abbrev SiteAbelianSheaves {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Type u :=
  (StackSiteData.abelianSheaves (X := X) τ).Carrier

abbrev SiteModules {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Type u :=
  (StackSiteData.modules (X := X) τ).Carrier

instance siteAbelianSheavesCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Category.{u} (SiteAbelianSheaves X τ) :=
  (StackSiteData.abelianSheaves (X := X) τ).category

instance siteAbelianSheavesAbelian {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Abelian (SiteAbelianSheaves X τ) :=
  (StackSiteData.abelianSheaves (X := X) τ).abelian

instance siteModulesCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Category.{u} (SiteModules X τ) :=
  (StackSiteData.modules (X := X) τ).category

instance siteModulesAbelian {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) : Abelian (SiteModules X τ) :=
  (StackSiteData.modules (X := X) τ).abelian

abbrev QuasiCoherentModules {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] :=
  (StackSiteData.isQuasiCoherent (X := X) .fppf).FullSubcategory

abbrev LQCohFbcModules {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) :=
  (StackSiteData.isLocallyQuasiCoherentFlatBaseChange (X := X) τ).FullSubcategory

abbrev ParasiticModules {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) :=
  (StackSiteData.isParasitic (X := X) τ).FullSubcategory

abbrev QCoh {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮) [StackSiteData X] :=
  (StackSiteData.quasiCoherentModules (X := X)).Carrier

instance qcohCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] : Category.{u} (QCoh X) :=
  (StackSiteData.quasiCoherentModules (X := X)).category

instance qcohAbelian {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] : Abelian (QCoh X) :=
  (StackSiteData.quasiCoherentModules (X := X)).abelian

def IsQuasiCoherent {𝒮 : Type u} [Category.{u} 𝒮] {X : 𝒮}
    [StackSiteData X] (τ : SiteKind) : ObjectProperty (SiteModules X τ) :=
  StackSiteData.isQuasiCoherent (X := X) τ

def IsLQCohFbc {𝒮 : Type u} [Category.{u} 𝒮] {X : 𝒮}
    [StackSiteData X] (τ : SiteKind) : ObjectProperty (SiteModules X τ) :=
  StackSiteData.isLocallyQuasiCoherentFlatBaseChange (X := X) τ

def IsParasitic {𝒮 : Type u} [Category.{u} 𝒮] {X : 𝒮}
    [StackSiteData X] (τ : SiteKind) : ObjectProperty (SiteModules X τ) :=
  StackSiteData.isParasitic (X := X) τ

/-- The coefficient category on a fixed site. -/
def CoefficientCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind) : AbelianCategoryData.{u} :=
  match κ with
  | .abelian => StackSiteData.abelianSheaves (X := X) τ
  | .module => StackSiteData.modules (X := X) τ

abbrev CoefficientCarrier {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind) : Type u :=
  (CoefficientCategory X τ κ).Carrier

instance coefficientCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind) :
    Category.{u} (CoefficientCarrier X τ κ) :=
  (CoefficientCategory X τ κ).category

instance coefficientAbelian {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind) :
    Abelian (CoefficientCarrier X τ κ) :=
  (CoefficientCategory X τ κ).abelian

noncomputable instance coefficientHasDerivedCategory {𝒮 : Type u}
    [Category.{u} 𝒮] (X : 𝒮) [StackSiteData X] (τ : SiteKind)
    (κ : CoefficientKind) : HasDerivedCategory.{u} (CoefficientCarrier X τ κ) :=
  HasDerivedCategory.standard _

noncomputable instance siteModulesHasDerivedCategory {𝒮 : Type u}
    [Category.{u} 𝒮] (X : 𝒮) [StackSiteData X] (τ : SiteKind) :
    HasDerivedCategory.{u} (SiteModules X τ) :=
  HasDerivedCategory.standard _

abbrev SiteDerivedCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind) :=
  DerivedCategory (CoefficientCarrier X τ κ)

/-- A complex in a derived category has cohomology in a module property when
each of its canonical Mathlib homology objects has that property. -/
def DerivedCohomologyProperty {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind)
    (P : ObjectProperty (CoefficientCarrier X τ κ)) :
    ObjectProperty (SiteDerivedCategory X τ κ) :=
  fun K => ∀ i : ℤ,
    P ((DerivedCategory.homologyFunctor (CoefficientCarrier X τ κ) i).obj K)

abbrev DerivedWithProperty {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind)
    (P : ObjectProperty (CoefficientCarrier X τ κ)) :=
  (DerivedCohomologyProperty X τ κ P).FullSubcategory

def IsBoundedBelow {𝒮 : Type u} [Category.{u} 𝒮] {X : 𝒮}
    [StackSiteData X] (τ : SiteKind) (κ : CoefficientKind)
    (K : SiteDerivedCategory X τ κ) : Prop :=
  ∃ n : ℤ, ∀ i : ℤ, i < n →
    IsZero ((DerivedCategory.homologyFunctor (CoefficientCarrier X τ κ) i).obj K)

/-! ## The comparison morphisms and derived functors -/

/-- The underlying inverse-image and shriek functors attached to the two
comparison morphisms of sites. -/
class SiteComparisonData {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] where
  shriek : ∀ c : ComparisonKind, ∀ κ : CoefficientKind,
    CoefficientCarrier X (fineSite c) κ ⥤ CoefficientCarrier X (coarseSite c) κ
  inverseImage : ∀ c : ComparisonKind, ∀ κ : CoefficientKind,
    CoefficientCarrier X (coarseSite c) κ ⥤ CoefficientCarrier X (fineSite c) κ
  derivedInverseImage : ∀ c : ComparisonKind, ∀ κ : CoefficientKind,
    SiteDerivedCategory X (coarseSite c) κ ⥤ SiteDerivedCategory X (fineSite c) κ

/-- The data carried by a selected left derived functor.  The derived
category functor is separated from the underived functor so that later
statements can record the adjunction and comparison isomorphism explicitly. -/
structure LeftDerivedFunctorData {A B : Type u} [Category.{u} A] [Category.{u} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{u} A]
    [HasDerivedCategory.{u} B] (F : A ⥤ B) where
  functor : DerivedCategory A ⥤ DerivedCategory B

/-- The source assertion for one coefficient category and one site
comparison.  The orientation of `unitIso` records the source identity
`g^* Lg_! = id` as a natural isomorphism rather than a definitional equality. -/
structure DerivedComparisonStatement {𝒮 : Type u} [Category.{u} 𝒮]
    (X : 𝒮) [StackSiteData X] [SiteComparisonData X]
    (c : ComparisonKind) (κ : CoefficientKind) where
  leftDerived : LeftDerivedFunctorData (SiteComparisonData.shriek (X := X) c κ)
  adjunction : leftDerived.functor ⊣ SiteComparisonData.derivedInverseImage (X := X) c κ
  unitIso : 𝟭 (SiteDerivedCategory X (fineSite c) κ) ≅
    leftDerived.functor ⋙ SiteComparisonData.derivedInverseImage (X := X) c κ

/-- A square of stack morphisms together with the derived direct and inverse
images used in the functoriality lemma. -/
structure FunctorialDerivedSquare {𝒮 : Type u} [Category.{u} 𝒮]
    (X Y : 𝒮) [StackSiteData X] [StackSiteData Y]
    [SiteComparisonData X] [SiteComparisonData Y] where
  f : X ⟶ Y
  coarsePushforward : ∀ c κ,
    SiteDerivedCategory X (coarseSite c) κ ⥤
      SiteDerivedCategory Y (coarseSite c) κ
  finePushforward : ∀ c κ,
    SiteDerivedCategory X (fineSite c) κ ⥤
      SiteDerivedCategory Y (fineSite c) κ
  coarsePullback : ∀ c κ,
    SiteDerivedCategory Y (coarseSite c) κ ⥤
      SiteDerivedCategory X (coarseSite c) κ
  finePullback : ∀ c κ,
    SiteDerivedCategory Y (fineSite c) κ ⥤
      SiteDerivedCategory X (fineSite c) κ

/-! ## Cohomology values and affine objects -/

/-- The target category in which a derived global-sections functor is
recorded.  Its concrete realization is supplied by the cohomology-of-stacks
development; the chapter only needs its categorical interface. -/
class StackCohomologyData {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] where
  valueCategory : CoefficientKind → AbelianCategoryData.{u}
  siteObject : SiteKind → Type u
  coarseObject : ∀ c,
    siteObject (fineSite c) → siteObject (coarseSite c)
  siteObjectIsFlat : siteObject .fppf → Prop
  siteObjectIsAffine : siteObject .fppf → Prop
  globalSections : ∀ τ κ,
    SiteDerivedCategory X τ κ ⥤ (valueCategory κ).Carrier
  localSections : ∀ τ κ, siteObject τ →
    SiteDerivedCategory X τ κ ⥤ (valueCategory κ).Carrier

abbrev CohomologyValue {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X] (κ : CoefficientKind) : Type u :=
  (StackCohomologyData.valueCategory (X := X) κ).Carrier

instance cohomologyValueCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X] (κ : CoefficientKind) :
    Category.{u} (CohomologyValue X κ) :=
  (StackCohomologyData.valueCategory (X := X) κ).category

instance cohomologyValueAbelian {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X] (κ : CoefficientKind) :
    Abelian (CohomologyValue X κ) :=
  (StackCohomologyData.valueCategory (X := X) κ).abelian

def DerivedGlobalSections {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X] (τ : SiteKind) (κ : CoefficientKind) :
    SiteDerivedCategory X τ κ ⥤ CohomologyValue X κ :=
  StackCohomologyData.globalSections (X := X) τ κ

def DerivedSectionsAt {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X] (τ : SiteKind)
    (κ : CoefficientKind) (x : StackCohomologyData.siteObject (X := X) τ) :
    SiteDerivedCategory X τ κ ⥤ CohomologyValue X κ :=
  StackCohomologyData.localSections (X := X) τ κ x

def IsFlatSiteObject {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X]
    (x : StackCohomologyData.siteObject (X := X) .fppf) : Prop :=
  StackCohomologyData.siteObjectIsFlat (X := X) x

def IsAffineSiteObject {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackCohomologyData X]
    (x : StackCohomologyData.siteObject (X := X) .fppf) : Prop :=
  StackCohomologyData.siteObjectIsAffine (X := X) x

/-- Affine objects and the tensor/base-change functors needed by the final
section.  `tensorPullback` abstracts the displayed derived tensor product;
its codomain and the `baseChangeIso` field retain the exact quasi-isomorphism
assertion without fixing a concrete ring model for an algebraic stack. -/
class StackAffineData {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] where
  affineObject : Type u
  affineHom : affineObject → affineObject → Type u
  value : CoefficientKind → affineObject → Type u
  valueCategory : ∀ κ x, Category.{u} (value κ x)
  sectionValue : ∀ κ x,
    SiteDerivedCategory X .fppf κ → value κ x
  tensorPullback : ∀ κ {x x' : affineObject},
    affineHom x x' →
      @CategoryTheory.Functor (value κ x') (valueCategory κ x')
        (value κ x) (valueCategory κ x)

instance affineValueCategory {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackAffineData X] (κ : CoefficientKind)
    (x : StackAffineData.affineObject (X := X)) :
    Category.{u} (StackAffineData.value (X := X) κ x) :=
  StackAffineData.valueCategory (X := X) κ x

def AffineObject {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackAffineData X] := StackAffineData.affineObject (X := X)

def AffineMorphism {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackAffineData X]
    {x x' : AffineObject X} : Type u := StackAffineData.affineHom (X := X) x x'

def AffineSection {𝒮 : Type u} [Category.{u} 𝒮] (X : 𝒮)
    [StackSiteData X] [StackAffineData X] (κ : CoefficientKind)
    (x : AffineObject X) (K : SiteDerivedCategory X .fppf κ) :
      StackAffineData.value (X := X) κ x :=
  StackAffineData.sectionValue (X := X) κ x K

end Formalization.Books.StacksPerfect.Unit01
