import Formalization.Books.MoreAlgebra.Unit75.PerfectComplexes
import Formalization.Books.MoreAlgebra.Unit60.DerivedBaseChange

/-!
# More on Algebra, Chapter 100: Base change for derived hom

The source identifies derived Hom after extension of scalars and then studies
the canonical base-change map.  The derived categories, extension/restriction
functors, RHom, and finiteness predicates below are the canonical interfaces
from earlier chapters; this file records the chapter-specific comparison maps
and the four hypotheses under which the base-change map is invertible.
-/

noncomputable section

open CategoryTheory
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit60
open Formalization.Books.MoreAlgebra.Unit65
open Formalization.Books.MoreAlgebra.Unit67
open Formalization.Books.MoreAlgebra.Unit74
open Formalization.Books.MoreAlgebra.Unit75

universe w u

namespace Formalization.Books.MoreAlgebra.Unit100

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] := Unit60.D R

/- The first source lemma uses the natural `R'`-module structure on the
derived Hom over `R`.  A same-ring `Unit74.RHom` object lives in `D(R)`, so
the cross-ring object is exposed by this small canonical interface. -/
structure RelativeRHomData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) where
  functor : (D R)ᵒᵖ × D A ⥤ D A
  upgrade : ∀ (K : D R) (M : D A),
    functor.obj (Opposite.op K, M) ≅
      RHom (R := A) ((derivedBaseChangeFunctor f).obj K) M
  restriction : ∀ (K : D R) (M : D A),
    RHom (R := R) K ((derivedRestrictionFunctor f).obj M) ≅
      (derivedRestrictionFunctor f).obj (functor.obj (Opposite.op K, M))

theorem relativeRHomData_exists
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    Nonempty (RelativeRHomData f) := by
  sorry

noncomputable def relativeRHomData
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    : RelativeRHomData f :=
  Classical.choice (relativeRHomData_exists f)

noncomputable abbrev relativeRHomFunctor
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A) :
    (D R)ᵒᵖ × D A ⥤ D A :=
  (relativeRHomData f).functor

noncomputable def relativeRHom
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (M : D A) : D A :=
  (relativeRHomFunctor f).obj (Opposite.op K, M)

theorem upgradeAdjointTensorRHom_exists
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (M : D A) :
    Nonempty (relativeRHom f K M ≅
      RHom (R := A) ((derivedBaseChangeFunctor f).obj K) M) := by
  exact ⟨(relativeRHomData f).upgrade K M⟩

noncomputable def upgradeAdjointTensorRHom
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (M : D A) :
    relativeRHom f K M ≅
      RHom (R := A) ((derivedBaseChangeFunctor f).obj K) M :=
  Classical.choice (upgradeAdjointTensorRHom_exists f K M)

theorem relativeRHom_restriction_exists
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (M : D A) :
    Nonempty (RHom (R := R) K ((derivedRestrictionFunctor f).obj M) ≅
      (derivedRestrictionFunctor f).obj (relativeRHom f K M)) := by
  exact ⟨(relativeRHomData f).restriction K M⟩

noncomputable def relativeRHom_restrictionIso
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K : D R) (M : D A) :
    RHom (R := R) K ((derivedRestrictionFunctor f).obj M) ≅
      (derivedRestrictionFunctor f).obj (relativeRHom f K M) :=
  Classical.choice (relativeRHom_restriction_exists f K M)

/- The displayed map is functorial in both derived arguments.  Its body is
the adjoint transpose of the map induced by the unit
`M ⟶ Res (M ⊗ᴸ_R R')`, followed by the upgrade isomorphism above. -/
noncomputable def baseChangeRHomMap
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K M : D R) :
    (derivedBaseChangeFunctor f).obj (RHom (R := R) K M) ⟶
      RHom (R := A) ((derivedBaseChangeFunctor f).obj K)
        ((derivedBaseChangeFunctor f).obj M) :=
  let adj := Classical.choice (derivedBaseChange_leftAdjoint_restriction f)
  let g :=
    rHomMap (R := R) (𝟙 K) (adj.unit.app M) ≫
      (relativeRHom_restrictionIso f K
        ((derivedBaseChangeFunctor f).obj M)).hom
  let h :=
    (adj.homEquiv (RHom (R := R) K M)
      (relativeRHom f K ((derivedBaseChangeFunctor f).obj M))).symm g
  h ≫ (upgradeAdjointTensorRHom f K
    ((derivedBaseChangeFunctor f).obj M)).hom

theorem baseChangeRHomMap_natural
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    {K K' M M' : D R} (fK : K' ⟶ K) (fM : M ⟶ M') :
    baseChangeRHomMap f K M ≫
        rHomMap (R := A) ((derivedBaseChangeFunctor f).map fK)
          ((derivedBaseChangeFunctor f).map fM) =
      (derivedBaseChangeFunctor f).map (rHomMap (R := R) fK fM) ≫
        baseChangeRHomMap f K' M' := by
  sorry

/- The four alternatives in the source lemma are exposed separately so each
criterion can be used without unpacking a disjunction. -/
theorem baseChangeRHomMap_isIso_of_perfect
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K M : D R) (hK : Perfect R K) :
    IsIso (baseChangeRHomMap f K M) := by
  sorry

theorem baseChangeRHomMap_isIso_of_perfect_base_ring
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K M : D R) (hA : PerfectModule R (ringMapModule f)) :
    IsIso (baseChangeRHomMap f K M) := by
  sorry

theorem baseChangeRHomMap_isIso_of_flat_pseudoCoherent
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K M : D R) (hf : f.Flat) (hK : IsPseudoCoherent R K)
    (hM : derivedPlusProperty (ModuleCat.{u} R) M) :
    IsIso (baseChangeRHomMap f K M) := by
  sorry

theorem baseChangeRHomMap_isIso_of_finite_tor_dimension
    {R A : Type u} [CommRing R] [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (f : R →+* A)
    (K M : D R)
    (hA : ModuleHasFiniteTorDimension R (ringMapModule f))
    (hK : IsPseudoCoherent R K)
    (hM : derivedPlusProperty (ModuleCat.{u} R) M) :
    IsIso (baseChangeRHomMap f K M) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit100
