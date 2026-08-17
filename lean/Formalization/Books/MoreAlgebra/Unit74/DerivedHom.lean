import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.MoreAlgebra.Unit73.SignRules

/-!
# More on Algebra, Chapter 74: derived hom

The source uses the unbounded derived category of modules and computes derived
Hom by an ordinary Hom complex into a K-injective representative.  Mathlib
already supplies the derived category, its quotient functor, K-injective
complexes, and the Hom-complex construction from the preceding chapters.  The
interfaces below package the two derived operations and the canonical maps used
in this section without introducing a competing derived-category model.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.MoreAlgebra.Unit73

universe u w

namespace Formalization.Books.MoreAlgebra.Unit74

/-! ## The derived category and derived tensor product -/

abbrev Comp (R : Type u) [CommRing R] :=
  Formalization.Books.MoreAlgebra.Unit73.Comp R

abbrev D (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :=
  DerivedCategory (ModuleCat.{u} R)

noncomputable abbrev derivedQuotient (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Comp R ⥤ D R :=
  DerivedCategory.Q

/- A complex is K-flat when tensoring by it preserves quasi-isomorphisms.
   This is the property used by the source's derived-tensor computations. -/
def IsKFlat {R : Type u} [CommRing R]
    (K : Comp R) : Prop :=
  ∀ {L M : Comp R} (f : L ⟶ M), QuasiIso f →
    QuasiIso ((tensorLeftComplexFunctor R K).map f)

/- A bifunctor with the source's K-flat representative computation.  The
   existence theorem is the only unresolved part of this foundational choice;
   the operation itself is a genuine Lean body. -/
structure DerivedTensorFunctorData (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  functor : D R × D R ⥤ D R
  represented :
    ∀ (K L : D R), ∃ (K' L' : Comp R)
      (_eK : (derivedQuotient R).obj K' ≅ K)
      (_eL : (derivedQuotient R).obj L' ≅ L),
      IsKFlat K' ∧ IsKFlat L' ∧
        Nonempty (functor.obj (K, L) ≅
          (derivedQuotient R).obj (tensorProductComplex R K' L'))

theorem derivedTensorFunctorData_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (DerivedTensorFunctorData R) := by
  sorry

noncomputable def derivedTensorFunctor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] : D R × D R ⥤ D R :=
  (Classical.choice (derivedTensorFunctorData_exists (R := R))).functor

noncomputable def derivedTensor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) : D R :=
  (derivedTensorFunctor (R := R)).obj (K, L)

noncomputable def derivedTensorMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L L' : D R} (f : K ⟶ K') (g : L ⟶ L') :
    derivedTensor (R := R) K L ⟶ derivedTensor (R := R) K' L' :=
  (derivedTensorFunctor (R := R)).map (f, g)

theorem derivedTensor_represented {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) :
    ∃ (K' L' : Comp R)
      (_eK : (derivedQuotient R).obj K' ≅ K)
      (_eL : (derivedQuotient R).obj L' ≅ L),
      IsKFlat K' ∧ IsKFlat L' ∧
        Nonempty (derivedTensor (R := R) K L ≅
          (derivedQuotient R).obj (tensorProductComplex R K' L')) := by
  sorry

/-! ## Derived Hom -/

/- The representation field is the precise source construction: for a complex
   `L` and a K-injective complex `I`, derived Hom is represented by the
   ordinary Hom complex `Hom^•(L, I)`. -/
structure DerivedHomFunctorData (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  functor : (D R)ᵒᵖ × D R ⥤ D R
  onKInjective :
    ∀ (L I : Comp R), CochainComplex.IsKInjective I →
      Nonempty (functor.obj
          (Opposite.op ((derivedQuotient R).obj L), (derivedQuotient R).obj I) ≅
        (derivedQuotient R).obj (homComplex L I))

theorem derivedHomFunctorData_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (DerivedHomFunctorData R) := by
  sorry

noncomputable def derivedHomFunctorData {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedHomFunctorData R :=
  Classical.choice (derivedHomFunctorData_exists (R := R))

noncomputable abbrev derivedHomFunctor {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    (D R)ᵒᵖ × D R ⥤ D R :=
  (derivedHomFunctorData (R := R)).functor

noncomputable def RHom {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) : D R :=
  (derivedHomFunctor (R := R)).obj (Opposite.op K, L)

/- The map API exposes the contravariance in the first variable and the
   covariance in the second variable supplied by the chosen functor. -/
noncomputable def rHomMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L L' : D R} (f : K' ⟶ K) (g : L ⟶ L') :
    RHom (R := R) K L ⟶ RHom (R := R) K' L' :=
  (derivedHomFunctor (R := R)).map (f.op, g)

theorem rHom_on_KInjective {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (L I : Comp R) (hI : CochainComplex.IsKInjective I) :
    Nonempty (RHom (R := R) ((derivedQuotient R).obj L) ((derivedQuotient R).obj I) ≅
      (derivedQuotient R).obj (homComplex L I)) := by
  exact (derivedHomFunctorData (R := R)).onKInjective L I hI

/- Independence of the K-injective representative is the well-definedness
   assertion made immediately after the cohomology formula in the source. -/
theorem rHom_KInjective_independent {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (L I J : Comp R)
    (hI : CochainComplex.IsKInjective I)
    (hJ : CochainComplex.IsKInjective J)
    (e : (derivedQuotient R).obj I ≅ (derivedQuotient R).obj J) :
    Nonempty ((derivedQuotient R).obj (homComplex L I) ≅
      (derivedQuotient R).obj (homComplex L J)) := by
  sorry

/-! ## The internal-Hom characterization and cohomology -/

theorem internalHom_morphism_equiv_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : D R) :
    Nonempty ((K ⟶ RHom (R := R) L M) ≃
      (derivedTensor (R := R) K L ⟶ M)) := by
  sorry

noncomputable def internalHomMorphismEquiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L M : D R) :
    (K ⟶ RHom (R := R) L M) ≃ (derivedTensor (R := R) K L ⟶ M) :=
  Classical.choice (internalHom_morphism_equiv_exists K L M)

theorem rHom_cohomology_equiv_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (L M : D R) (n : ℤ) :
    Nonempty (((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj
        (RHom (R := R) L M) : Type u) ≃+
      (L ⟶ (CategoryTheory.shiftFunctor (D R) n).obj M)) := by
  sorry

noncomputable def rHom_cohomology_equiv {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (L M : D R) (n : ℤ) :
    ((derivedCohomologyFunctor (ModuleCat.{u} R) n).obj
        (RHom (R := R) L M) : Type u) ≃+
      (L ⟶ (CategoryTheory.shiftFunctor (D R) n).obj M) :=
  Classical.choice (rHom_cohomology_equiv_exists L M n)

/-! ## The internal-Hom isomorphism -/

structure InternalHomIsoFamily (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  app : ∀ K L M : D R,
    RHom (R := R) K (RHom (R := R) L M) ≅
      RHom (R := R) (derivedTensor (R := R) K L) M
  natural :
    ∀ {K K' L L' M M' : D R} (fK : K' ⟶ K) (fL : L' ⟶ L)
      (fM : M ⟶ M'),
      (app K L M).hom ≫ rHomMap (R := R) (derivedTensorMap (R := R) fK fL) fM =
        rHomMap (R := R) fK (rHomMap (R := R) fL fM) ≫ (app K' L' M').hom

theorem internalHomIsoFamily_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (InternalHomIsoFamily R) := by
  sorry

noncomputable def internalHomIsoFamily {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    InternalHomIsoFamily R :=
  Classical.choice (internalHomIsoFamily_exists (R := R))

noncomputable def internalHomIso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L M : D R) :
    RHom (R := R) K (RHom (R := R) L M) ≅
      RHom (R := R) (derivedTensor (R := R) K L) M :=
  (internalHomIsoFamily (R := R)).app K L M

theorem internalHomIso_natural {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L L' M M' : D R} (fK : K' ⟶ K) (fL : L' ⟶ L)
    (fM : M ⟶ M') :
    (internalHomIso (R := R) K L M).hom ≫
        rHomMap (R := R) (derivedTensorMap (R := R) fK fL) fM =
      rHomMap (R := R) fK (rHomMap (R := R) fL fM) ≫
        (internalHomIso (R := R) K' L' M').hom := by
  exact (internalHomIsoFamily (R := R)).natural fK fL fM

/-! ## Hom out of a bounded-above projective complex -/

def IsTermwiseProjective {R : Type u} [CommRing R] (P : Comp R) : Prop :=
  ∀ n : ℤ, Module.Projective R (P.X n : Type u)

theorem rHom_out_of_boundedAbove_projective {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P L : Comp R)
    (hP : IsBoundedAbove P)
    (hPprojective : IsTermwiseProjective P) :
    Nonempty (RHom (R := R) ((derivedQuotient R).obj P) ((derivedQuotient R).obj L) ≅
      (derivedQuotient R).obj (homComplex P L)) := by
  sorry

/-! ## Evaluation -/

structure InternalHomEvaluationFamily (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  app : ∀ K L M : D R,
    derivedTensor (R := R) (RHom (R := R) L M) K ⟶
      RHom (R := R) (RHom (R := R) K L) M
  natural :
    ∀ {K K' L L' M M' : D R} (fK : K ⟶ K') (fL : L' ⟶ L)
      (fM : M ⟶ M'),
      app K L M ≫ rHomMap (R := R) (rHomMap (R := R) fK fL) fM =
        derivedTensorMap (R := R) (rHomMap (R := R) fL fM) fK ≫ app K' L' M'

theorem internalHomEvaluationFamily_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (InternalHomEvaluationFamily R) := by
  sorry

noncomputable def internalHomEvaluationFamily {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    InternalHomEvaluationFamily R :=
  Classical.choice (internalHomEvaluationFamily_exists (R := R))

noncomputable def internalHomEvaluationMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L M : D R) :
    derivedTensor (R := R) (RHom (R := R) L M) K ⟶
      RHom (R := R) (RHom (R := R) K L) M :=
  (internalHomEvaluationFamily (R := R)).app K L M

theorem internalHomEvaluationMap_natural {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L L' M M' : D R} (fK : K ⟶ K') (fL : L' ⟶ L)
    (fM : M ⟶ M') :
    internalHomEvaluationMap (R := R) K L M ≫
          rHomMap (R := R) (rHomMap (R := R) fK fL) fM =
      derivedTensorMap (R := R) (rHomMap (R := R) fL fM) fK ≫
        internalHomEvaluationMap (R := R) K' L' M' := by
  exact (internalHomEvaluationFamily (R := R)).natural fK fL fM

/-! ## Composition -/

structure InternalHomCompositionFamily (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  app : ∀ K L M : D R,
    derivedTensor (R := R) (RHom (R := R) L M) (RHom (R := R) K L) ⟶
      RHom (R := R) K M
  natural :
    ∀ {K K' L M M' : D R} (fK : K' ⟶ K) (fM : M ⟶ M'),
      app K L M ≫ rHomMap (R := R) fK fM =
        derivedTensorMap (R := R) (rHomMap (R := R) (𝟙 L) fM)
          (rHomMap (R := R) fK (𝟙 L)) ≫
          app K' L M'
  dinatural_middle :
    ∀ {K L L' M : D R} (f : L ⟶ L'),
      derivedTensorMap (R := R) (rHomMap (R := R) f (𝟙 M))
          (𝟙 (RHom (R := R) K L)) ≫ app K L M =
        derivedTensorMap (R := R) (𝟙 (RHom (R := R) L' M))
          (rHomMap (R := R) (𝟙 K) f) ≫ app K L' M

theorem internalHomCompositionFamily_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (InternalHomCompositionFamily R) := by
  sorry

noncomputable def internalHomCompositionFamily {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    InternalHomCompositionFamily R :=
  Classical.choice (internalHomCompositionFamily_exists (R := R))

noncomputable def internalHomCompositionMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L M : D R) :
    derivedTensor (R := R) (RHom (R := R) L M) (RHom (R := R) K L) ⟶
      RHom (R := R) K M :=
  (internalHomCompositionFamily (R := R)).app K L M

theorem internalHomCompositionMap_natural {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L M M' : D R} (fK : K' ⟶ K) (fM : M ⟶ M') :
    internalHomCompositionMap (R := R) K L M ≫ rHomMap (R := R) fK fM =
      derivedTensorMap (R := R) (rHomMap (R := R) (𝟙 L) fM)
          (rHomMap (R := R) fK (𝟙 L)) ≫
        internalHomCompositionMap (R := R) K' L M' := by
  exact (internalHomCompositionFamily (R := R)).natural fK fM

theorem internalHomCompositionMap_dinatural_middle {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K L L' M : D R} (f : L ⟶ L') :
    derivedTensorMap (R := R) (rHomMap (R := R) f (𝟙 M))
          (𝟙 (RHom (R := R) K L)) ≫
          internalHomCompositionMap (R := R) K L M =
      derivedTensorMap (R := R) (𝟙 (RHom (R := R) L' M))
          (rHomMap (R := R) (𝟙 K) f) ≫
        internalHomCompositionMap (R := R) K L' M := by
  exact (internalHomCompositionFamily (R := R)).dinatural_middle f

/-! ## The two diagonal maps -/

structure InternalHomDiagonalBetterFamily (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  app : ∀ K L M : D R,
    derivedTensor (R := R) K (RHom (R := R) M L) ⟶
      RHom (R := R) M (derivedTensor (R := R) K L)
  natural :
    ∀ {K K' L L' M M' : D R} (fK : K ⟶ K') (fL : L ⟶ L')
      (fM : M' ⟶ M),
      app K L M ≫
          rHomMap (R := R) fM (derivedTensorMap (R := R) fK fL) =
        derivedTensorMap (R := R) fK (rHomMap (R := R) fM fL) ≫
          app K' L' M'

theorem internalHomDiagonalBetterFamily_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (InternalHomDiagonalBetterFamily R) := by
  sorry

noncomputable def internalHomDiagonalBetterFamily {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    InternalHomDiagonalBetterFamily R :=
  Classical.choice (internalHomDiagonalBetterFamily_exists (R := R))

noncomputable def internalHomDiagonalBetterMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L M : D R) :
    derivedTensor (R := R) K (RHom (R := R) M L) ⟶
      RHom (R := R) M (derivedTensor (R := R) K L) :=
  (internalHomDiagonalBetterFamily (R := R)).app K L M

theorem internalHomDiagonalBetterMap_natural {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L L' M M' : D R} (fK : K ⟶ K') (fL : L ⟶ L')
    (fM : M' ⟶ M) :
    internalHomDiagonalBetterMap (R := R) K L M ≫
          rHomMap (R := R) fM (derivedTensorMap (R := R) fK fL) =
      derivedTensorMap (R := R) fK (rHomMap (R := R) fM fL) ≫
        internalHomDiagonalBetterMap (R := R) K' L' M' := by
  exact (internalHomDiagonalBetterFamily (R := R)).natural fK fL fM

structure InternalHomDiagonalFamily (R : Type u) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] where
  app : ∀ K L : D R, K ⟶
    RHom (R := R) L (derivedTensor (R := R) K L)
  natural_first :
    ∀ {K K' L : D R} (f : K ⟶ K'),
      f ≫ app K' L =
      app K L ≫
        rHomMap (R := R) (𝟙 L) (derivedTensorMap (R := R) f (𝟙 L))
  dinatural_second :
    ∀ {K L L' : D R} (f : L ⟶ L'),
      app K L' ≫
          rHomMap (R := R) f (𝟙 (derivedTensor (R := R) K L')) =
        app K L ≫
          rHomMap (R := R) (𝟙 L) (derivedTensorMap (R := R) (𝟙 K) f)

theorem internalHomDiagonalFamily_exists {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    Nonempty (InternalHomDiagonalFamily R) := by
  sorry

noncomputable def internalHomDiagonalFamily {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    InternalHomDiagonalFamily R :=
  Classical.choice (internalHomDiagonalFamily_exists (R := R))

noncomputable def internalHomDiagonalMap {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (K L : D R) :
    K ⟶ RHom (R := R) L (derivedTensor (R := R) K L) :=
  (internalHomDiagonalFamily (R := R)).app K L

theorem internalHomDiagonalMap_natural_first {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K K' L : D R} (f : K ⟶ K') :
    f ≫ internalHomDiagonalMap (R := R) K' L =
      internalHomDiagonalMap (R := R) K L ≫
        rHomMap (R := R) (𝟙 L) (derivedTensorMap (R := R) f (𝟙 L)) := by
  exact (internalHomDiagonalFamily (R := R)).natural_first f

theorem internalHomDiagonalMap_dinatural_second {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {K L L' : D R} (f : L ⟶ L') :
    internalHomDiagonalMap (R := R) K L' ≫
          rHomMap (R := R) f (𝟙 (derivedTensor (R := R) K L')) =
      internalHomDiagonalMap (R := R) K L ≫
        rHomMap (R := R) (𝟙 L)
          (derivedTensorMap (R := R) (𝟙 K) f) := by
  exact (internalHomDiagonalFamily (R := R)).dinatural_second f

end Formalization.Books.MoreAlgebra.Unit74
