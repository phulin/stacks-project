import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit18.InjectiveResolutions

/-!
# Derived Categories, Chapter 23: resolution functors

The source identifies the bounded-below derived category of an abelian
category with the bounded-below homotopy category of injectives.  The
objectwise resolution data and its functorial upgrade are kept separate: the
first is the source's definition, while the second records the uniquely
compatible functor and natural isomorphism supplied by the comparison
property of injective complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit23

/-! ## The category of injectives and its derived comparison -/

/- Mathlib's `InjectiveObject` is the strictly full subcategory whose
   objects are the injectives of an abelian category. -/
abbrev InjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] : Type u :=
  CategoryTheory.InjectiveObject A

noncomputable instance injectiveSubcategory_additiveCategory
    {A : Type u} [Category.{v} A] [Abelian A] :
    AdditiveCategory (InjectiveSubcategory A) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/- The inclusion of complexes of injectives into complexes of `A`, followed
   by the bounded-below homotopy quotient, is the canonical model of
   `K⁺(I) ⥤ K⁺(A)`. -/
noncomputable def injectiveHomotopyInclusion
    {A : Type u} [Category.{v} A] [Abelian A] :
    KPlus (InjectiveSubcategory A) ⥤ KPlus A :=
  additiveHomotopyPlusFunctor (CategoryTheory.InjectiveObject.ι A)

/- The source's canonical functor `K⁺(I) ⥤ D⁺(A)`. -/
noncomputable def injectiveToDerivedFunctor
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    KPlus (InjectiveSubcategory A) ⥤ DPlus A :=
  injectiveHomotopyInclusion (A := A) ⋙ plusDerivedLocalizationFunctor A

private noncomputable def injectiveToDerivedFunctor_fullyFaithful
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] :
    (injectiveToDerivedFunctor (A := A)).FullyFaithful where
  preimage {X Y} f := by
    let ιF := (CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus
    let hι := Functor.FullyFaithful.ofFullyFaithful ιF
    let hI : CochainComplex.IsKInjective (ιF.obj Y).obj.as := by
      apply Formalization.Books.Derived.Unit18.isKInjective_of_bounded_below_termwise_injective
        _ ?_ (fun _ => inferInstance)
      obtain ⟨K, hK, hKY⟩ :=
        (ObjectProperty.strictMap_iff (CochainComplex.plus A)
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _).mp
          (ιF.obj Y).property
      rw [← hKY]
      rw [HomotopyCategory.quotient_obj_as]
      exact hK
    letI := hI
    exact hι.preimage
      (Classical.choose
        ((DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
          (ιF.obj X) (ιF.obj Y) (by infer_instance)).surjective f))
  map_preimage {X Y} f := by
    let ιF := (CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus
    let hι := Functor.FullyFaithful.ofFullyFaithful ιF
    let hI : CochainComplex.IsKInjective (ιF.obj Y).obj.as := by
      apply Formalization.Books.Derived.Unit18.isKInjective_of_bounded_below_termwise_injective
        _ ?_ (fun _ => inferInstance)
      obtain ⟨K, hK, hKY⟩ :=
        (ObjectProperty.strictMap_iff (CochainComplex.plus A)
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _).mp
          (ιF.obj Y).property
      rw [← hKY]
      rw [HomotopyCategory.quotient_obj_as]
      exact hK
    letI := hI
    let q := Classical.choose
      ((DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
        (ιF.obj X) (ιF.obj Y) (by infer_instance)).surjective f)
    have hq := Classical.choose_spec
      ((DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
        (ιF.obj X) (ιF.obj Y) (by infer_instance)).surjective f)
    change DerivedCategory.Plus.Qh.map (ιF.map (hι.preimage q)) = f
    rw [hι.map_preimage, hq]
  preimage_map {X Y} f := by
    let ιF := (CategoryTheory.InjectiveObject.ι A).mapHomotopyCategoryPlus
    let hι := Functor.FullyFaithful.ofFullyFaithful ιF
    let hI : CochainComplex.IsKInjective (ιF.obj Y).obj.as := by
      apply Formalization.Books.Derived.Unit18.isKInjective_of_bounded_below_termwise_injective
        _ ?_ (fun _ => inferInstance)
      obtain ⟨K, hK, hKY⟩ :=
        (ObjectProperty.strictMap_iff (CochainComplex.plus A)
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _).mp
          (ιF.obj Y).property
      rw [← hKY]
      rw [HomotopyCategory.quotient_obj_as]
      exact hK
    letI := hI
    apply hι.map_injective
    apply (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
      (ιF.obj X) (ιF.obj Y) (by infer_instance)).injective
    simpa [injectiveToDerivedFunctor, injectiveHomotopyInclusion,
      additiveHomotopyPlusFunctor, ιF] using
      Classical.choose_spec
        ((DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
          (ιF.obj X) (ιF.obj Y) (by infer_instance)).surjective
          (injectiveToDerivedFunctor.map f))

/- The proposition in the source is recorded with the established exact
   functor package and Mathlib's equivalence class.  The latter supplies the
   fully faithful and essentially-surjective assertions. -/
theorem injective_homotopy_to_derived_equivalence
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A] :
    Nonempty (ExactTriangulatedFunctorData (injectiveToDerivedFunctor (A := A))) ∧
      Functor.IsEquivalence (injectiveToDerivedFunctor (A := A)) := by
  refine ⟨?_, ?_⟩
  · let hι := Classical.choice
      ((additive_homotopy_functors_are_exact
        (CategoryTheory.InjectiveObject.ι A)).2.1)
    letI : (injectiveHomotopyInclusion (A := A)).CommShift ℤ := hι.commShift
    letI : (injectiveHomotopyInclusion (A := A)).IsTriangulated := hι.isTriangulated
    let hshift : (injectiveToDerivedFunctor (A := A)).CommShift ℤ := by
      dsimp [injectiveToDerivedFunctor]
      infer_instance
    letI := hshift
    refine ⟨{ commShift := hshift, isTriangulated := ?_ }⟩
    dsimp [injectiveToDerivedFunctor]
    infer_instance
  · let hFF := injectiveToDerivedFunctor_fullyFaithful (A := A)
    have hess : (injectiveToDerivedFunctor (A := A)).EssSurj := by
      dsimp [injectiveToDerivedFunctor, injectiveHomotopyInclusion,
        plusDerivedLocalizationFunctor, additiveHomotopyPlusFunctor]
      infer_instance
    exact ⟨hFF.faithful, hFF.full, hess⟩

private theorem kplus_homology_vanishes_below
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : KPlus A) :
    ∃ a : ℤ, ∀ n : ℤ, n < a → IsZero (K.obj.as.homology n) := by
  obtain ⟨L, hL, hLK⟩ :=
    (ObjectProperty.strictMap_iff (CochainComplex.plus A)
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _).mp K.property
  obtain ⟨a, ha⟩ := hL
  refine ⟨a, fun n hn => ?_⟩
  letI : L.IsStrictlyGE a := ha
  have hLzero : IsZero (L.homology n) := L.isZero_of_isGE a n hn
  let e : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ≅ K.obj :=
    eqToIso hLK
  have hKzero : IsZero
      ((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).obj K.obj) :=
    IsZero.of_iso hLzero
      (((HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).mapIso e).symm ≪≫
        (HomotopyCategory.homologyFunctorFactors A
          (ComplexShape.up ℤ) n).app L)
  let eK : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K.obj.as ≅ K.obj :=
    eqToIso (by rfl)
  exact IsZero.of_iso hKzero
    (((HomotopyCategory.homologyFunctorFactors A
        (ComplexShape.up ℤ) n).app K.obj.as).symm ≪≫
      (HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) n).mapIso eK)

private theorem resolution_object_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A]
    (K : KPlus A) :
    ∃ J : KPlus (InjectiveSubcategory A),
      ∃ i : K ⟶ (injectiveHomotopyInclusion (A := A)).obj J,
        quasiIsoPlusProperty A i := by
  obtain ⟨R⟩ :=
    Formalization.Books.Derived.Unit18.complex_injective_resolution_exists
      (kplus_homology_vanishes_below K)
  let L' : BookComplex (InjectiveSubcategory A) :=
    HomologicalComplex.liftObjectProperty _ R.target R.termwiseInjective
  have hL' : CochainComplex.plus (InjectiveSubcategory A) L' := by
    obtain ⟨a, ha⟩ := R.boundedBelow
    refine ⟨a, ?_⟩
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _
      (CategoryTheory.InjectiveObject.ι A)]
    exact ha
  let J : KPlus (InjectiveSubcategory A) :=
    (HomotopyCategory.Plus.quotient (InjectiveSubcategory A)).obj ⟨L', hL'⟩
  let i : K ⟶ (injectiveHomotopyInclusion (A := A)).obj J := by
    exact ObjectProperty.homMk
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map R.map)
  refine ⟨J, i, ?_⟩
  change (HomotopyCategory.Plus.quasiIso A) i
  rw [HomotopyCategory.Plus.quasiIso_iff]
  have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff R.map).2 R.quasiIso
  convert hq using 1
  · exact Subsingleton.elim _ _
  · cases K.obj
    rfl
  · rfl
  · rfl

/-! ## Objectwise resolution data -/

/-- The source's objectwise resolution choice on `K⁺(A)`: every object is
represented by a bounded-below complex of injectives and a quasi-isomorphism
from the original object. -/
structure ResolutionFunctorData
    (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The chosen bounded-below homotopy object of injectives. -/
  j : ∀ _K : KPlus A, KPlus (InjectiveSubcategory A)
  /-- The chosen quasi-isomorphism into the resolution. -/
  i : ∀ K : KPlus A,
    K ⟶ (injectiveHomotopyInclusion (A := A)).obj (j K)
  /-- The chosen map is a quasi-isomorphism in `K⁺(A)`. -/
  i_quasiIso : ∀ K : KPlus A, quasiIsoPlusProperty A (i K)

/- The image in `D⁺(A)` of the chosen map `i_K`. -/
noncomputable def resolutionDerivedComponent
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (K : KPlus A) :
    (plusDerivedLocalizationFunctor A).obj K ⟶
      (injectiveToDerivedFunctor (A := A)).obj (R.j K) :=
  (plusDerivedLocalizationFunctor A).map (R.i K)

/-! ## The uniquely compatible functorial upgrade -/

/-- A functorial upgrade of objectwise resolution data.

The component equation makes the natural isomorphism the one induced by the
chosen maps `i_K`, rather than an unrelated natural isomorphism. -/
structure ResolutionFunctorPackage
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) where
  /-- The functor `K⁺(A) ⥤ K⁺(I)`. -/
  functor : KPlus A ⥤ KPlus (InjectiveSubcategory A)
  /-- Its object function is the chosen object function of `R`. -/
  objectwise : ∀ K : KPlus A, functor.obj K = R.j K
  /-- The square with `D⁺(A)` commutes up to the comparison isomorphism. -/
  comparison :
    plusDerivedLocalizationFunctor A ≅
      functor ⋙ injectiveToDerivedFunctor (A := A)
  /-- The comparison isomorphism is induced by `i_K` in each component. -/
  comparison_component : ∀ K : KPlus A,
    comparison.hom.app K =
      (plusDerivedLocalizationFunctor A).map (R.i K) ≫
        eqToHom (congrArg
          (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X)
          (objectwise K).symm)

private noncomputable def resolution_component_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) (K : KPlus A) :
    (plusDerivedLocalizationFunctor A).obj K ≅
    (injectiveToDerivedFunctor (A := A)).obj (R.j K) := by
  letI : (plusDerivedLocalizationFunctor A).IsLocalization
      (quasiIsoPlusProperty A) :=
    plusDerivedLocalizationFunctor_is_localization A
  exact Localization.isoOfHom (plusDerivedLocalizationFunctor A)
    (quasiIsoPlusProperty A) (R.i K) (R.i_quasiIso K)

theorem resolution_functor_package_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) :
    Nonempty (ResolutionFunctorPackage R) := by
  let F := injectiveToDerivedFunctor (A := A)
  let Q := plusDerivedLocalizationFunctor A
  let hF := injectiveToDerivedFunctor_fullyFaithful (A := A)
  let e : ∀ K : KPlus A, Q.obj K ≅ F.obj (R.j K) :=
    fun K => resolution_component_iso R K
  let G : KPlus A ⥤ KPlus (InjectiveSubcategory A) :=
    { obj := R.j
      map := fun {K L} f =>
        hF.preimage ((e K).inv ≫ Q.map f ≫ (e L).hom)
      map_id := by
        intro K
        apply hF.map_injective
        rw [hF.map_preimage]
        simp
      map_comp := by
        intro K L M f g
        apply hF.map_injective
        rw [hF.map_preimage]
        simp [Category.assoc] }
  let c : Q ≅ G ⋙ F :=
    NatIso.ofComponents e (by
      intro K L f
      change Q.map f ≫ (e L).hom =
        (e K).hom ≫ F.map (hF.preimage ((e K).inv ≫ Q.map f ≫ (e L).hom))
      rw [hF.map_preimage]
      simp [Category.assoc])
  let P : ResolutionFunctorPackage R :=
    { functor := G
      objectwise := fun K => Eq.refl _
      comparison := c
      comparison_component := fun K => by
        change (e K).hom = Q.map (R.i K) ≫ 𝟙 _
        simp [e, resolution_component_iso, Localization.isoOfHom]
        change Q.map (R.i K) = Q.map (R.i K)
        rfl }
  exact ⟨P⟩

theorem resolution_functor_package_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    (R : ResolutionFunctorData A) :
    Subsingleton (ResolutionFunctorPackage R) := by
  let F := injectiveToDerivedFunctor (A := A)
  let Q := plusDerivedLocalizationFunctor A
  let hF := injectiveToDerivedFunctor_fullyFaithful (A := A)
  constructor
  intro P QP
  let hobj : ∀ K : KPlus A, P.functor.obj K = QP.functor.obj K :=
    fun K => (P.objectwise K).trans (QP.objectwise K).symm
  have hmap : ∀ (K L : KPlus A) (f : K ⟶ L),
      (injectiveToDerivedFunctor (A := A)).map (P.functor.map f) =
        eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
          (injectiveToDerivedFunctor (A := A)).obj X) (hobj K)) ≫
          (injectiveToDerivedFunctor (A := A)).map (QP.functor.map f) ≫
            eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
              (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm := by
    intro K L f
    have hp := P.comparison.hom.naturality f
    have hq := QP.comparison.hom.naturality f
    dsimp [Q] at hp hq ⊢
    have hpcomp : P.comparison.hom.app K ≫
        eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
          (injectiveToDerivedFunctor (A := A)).obj X) (hobj K)) =
            QP.comparison.hom.app K := by
      rw [P.comparison_component K, QP.comparison_component K]
      have hpobj :
          (plusDerivedLocalizationFunctor A).obj
              (injectiveHomotopyInclusion.obj (R.j K)) =
            (injectiveToDerivedFunctor (A := A)).obj (P.functor.obj K) := by
        calc
          _ = (injectiveToDerivedFunctor (A := A)).obj (R.j K) := by rfl
          _ = _ := congrArg _ (P.objectwise K).symm
      have hqobj :
          (plusDerivedLocalizationFunctor A).obj
              (injectiveHomotopyInclusion.obj (R.j K)) =
            (injectiveToDerivedFunctor (A := A)).obj (QP.functor.obj K) := by
        calc
          _ = (injectiveToDerivedFunctor (A := A)).obj (R.j K) := by rfl
          _ = _ := congrArg _ (QP.objectwise K).symm
      change ((plusDerivedLocalizationFunctor A).map (R.i K) ≫
          eqToHom hpobj) ≫
            eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
              (injectiveToDerivedFunctor (A := A)).obj X) (hobj K)) =
        (plusDerivedLocalizationFunctor A).map (R.i K) ≫ eqToHom hqobj
      simp only [Category.assoc, eqToHom_trans]
    have hqcomp : QP.comparison.hom.app L ≫
        eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
          (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm =
          P.comparison.hom.app L := by
      rw [P.comparison_component L, QP.comparison_component L]
      have hpobj :
          (plusDerivedLocalizationFunctor A).obj
              (injectiveHomotopyInclusion.obj (R.j L)) =
            (injectiveToDerivedFunctor (A := A)).obj (P.functor.obj L) := by
        calc
          _ = (injectiveToDerivedFunctor (A := A)).obj (R.j L) := by rfl
          _ = _ := congrArg _ (P.objectwise L).symm
      have hqobj :
          (plusDerivedLocalizationFunctor A).obj
              (injectiveHomotopyInclusion.obj (R.j L)) =
            (injectiveToDerivedFunctor (A := A)).obj (QP.functor.obj L) := by
        calc
          _ = (injectiveToDerivedFunctor (A := A)).obj (R.j L) := by rfl
          _ = _ := congrArg _ (QP.objectwise L).symm
      change ((plusDerivedLocalizationFunctor A).map (R.i L) ≫
          eqToHom hqobj) ≫
            eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
              (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm =
        (plusDerivedLocalizationFunctor A).map (R.i L) ≫ eqToHom hpobj
      simp only [Category.assoc, eqToHom_trans]
    apply (cancel_epi (P.comparison.hom.app K)).1
    calc
      P.comparison.hom.app K ≫ (injectiveToDerivedFunctor (A := A)).map
          (P.functor.map f) =
          Q.map f ≫ P.comparison.hom.app L := by
            simpa only [Functor.comp_map] using hp.symm
      _ = Q.map f ≫ QP.comparison.hom.app L ≫
          eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm := by
            simpa only [Category.assoc] using
              congrArg (fun t => Q.map f ≫ t) hqcomp.symm
      _ = QP.comparison.hom.app K ≫
          (injectiveToDerivedFunctor (A := A)).map (QP.functor.map f) ≫
          eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm := by
            have hq' : Q.map f ≫ QP.comparison.hom.app L =
                QP.comparison.hom.app K ≫
                  (injectiveToDerivedFunctor (A := A)).map (QP.functor.map f) := by
              simpa only [Q, Functor.comp_map] using hq
            simpa only [Category.assoc] using
              congrArg (fun t => t ≫ eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
                (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm) hq'
      _ = P.comparison.hom.app K ≫
          eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X) (hobj K)) ≫
          (injectiveToDerivedFunctor (A := A)).map (QP.functor.map f) ≫
          eqToHom (congrArg (fun X : KPlus (InjectiveSubcategory A) =>
            (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm := by
            simpa only [Category.assoc] using
              congrArg (fun t => t ≫ (injectiveToDerivedFunctor (A := A)).map
                (QP.functor.map f) ≫ eqToHom (congrArg
                  (fun X : KPlus (InjectiveSubcategory A) =>
                    (injectiveToDerivedFunctor (A := A)).obj X) (hobj L)).symm) hpcomp.symm
  have hfun : P.functor = QP.functor :=
    CategoryTheory.Functor.ext hobj (fun K L f => by
      apply hF.map_injective
      simpa [Functor.map_comp, eqToHom_map, Category.assoc] using hmap K L f)
  cases P with
  | mk Pf Pobj Pc Pcc =>
    cases QP with
    | mk Qf Qobj Qc Qcc =>
      cases hfun
      congr 1
      apply Iso.ext
      apply NatTrans.ext
      funext K
      rw [Pcc K, Qcc K]

/- A comparison between packages with different objectwise choices.  The
   compatibility equation is the precise meaning of “canonical” in the
   source's size remark. -/
structure ResolutionFunctorIso
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R S : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R)
    (Q : ResolutionFunctorPackage S) where
  /-- The unique natural isomorphism between the two resolution functors. -/
  iso : P.functor ≅ Q.functor
  /-- It is compatible with the two comparison isomorphisms to `D⁺(A)`. -/
  comm :
    P.comparison.hom ≫
        Functor.whiskerRight iso.hom (injectiveToDerivedFunctor (A := A)) =
      Q.comparison.hom

theorem resolution_functor_iso_exists_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R S : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) (Q : ResolutionFunctorPackage S) :
    Nonempty (ResolutionFunctorIso P Q) ∧
      Subsingleton (ResolutionFunctorIso P Q) := by
  let F := injectiveToDerivedFunctor (A := A)
  let hF := injectiveToDerivedFunctor_fullyFaithful (A := A)
  letI : F.Full := hF.full
  letI : F.Faithful := hF.faithful
  let c : P.functor ⋙ F ≅ Q.functor ⋙ F :=
    P.comparison.symm ≪≫ Q.comparison
  let iso : P.functor ≅ Q.functor :=
    Functor.fullyFaithfulCancelRight F c
  have hcomm : P.comparison.hom ≫
      Functor.whiskerRight iso.hom F = Q.comparison.hom := by
    apply NatTrans.ext
    funext K
    change P.comparison.hom.app K ≫ F.map (iso.hom.app K) =
      Q.comparison.hom.app K
    dsimp [iso]
    have hm : F.map (F.preimage (c.hom.app K)) = c.hom.app K :=
      F.map_preimage _
    rw [hm]
    simp [iso, c, F, Category.assoc]
  refine ⟨⟨{ iso := iso, comm := hcomm }⟩, ?_⟩
  constructor
  intro X Y
  have hiso : X.iso = Y.iso := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply hF.map_injective
    apply (cancel_epi (P.comparison.hom.app K)).1
    have hx := congrArg (fun t => t.app K) X.comm
    have hy := congrArg (fun t => t.app K) Y.comm
    simpa [Category.assoc] using hx.trans hy.symm
  cases X with
  | mk xi xc =>
    cases Y with
    | mk yi yc =>
      dsimp at hiso ⊢
      cases hiso
      rfl

/-! ## Existence and exactness -/

theorem resolution_functor_data_exists
    {A : Type u} [Category.{v} A] [Abelian A] [EnoughInjectives A] :
    Nonempty (ResolutionFunctorData A) := by
  classical
  choose j i hi using fun K : KPlus A => resolution_object_exists K
  exact ⟨{ j := j, i := i, i_quasiIso := hi }⟩

/- The source's existence statement: the objectwise choices can be upgraded
   to a functor and a compatible `2`-isomorphism. -/
theorem resolution_functor_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    [EnoughInjectives A] [HasDerivedCategory.{w} A] :
    ∃ R : ResolutionFunctorData A, Nonempty (ResolutionFunctorPackage R) := by
  obtain ⟨R⟩ := resolution_functor_data_exists (A := A)
  exact ⟨R, resolution_functor_package_exists R⟩

/- The source says that any resolution functor is exact.  The package from
   `Unit10` is exactly the shift-compatible triangulated-functor interface. -/
theorem resolution_functor_is_exact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) :
    Nonempty (ExactTriangulatedFunctorData P.functor) := by
  sorry

/- A quasi-inverse is recorded by the two standard natural isomorphisms;
   this is the source's “quasi-inverse to the canonical functor” language. -/
def QuasiInverseOf
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (G : D ⥤ C) : Prop :=
  Nonempty (𝟭 C ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 D)

theorem resolution_functor_quasi_inverse
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A]
    {R : ResolutionFunctorData A}
    (P : ResolutionFunctorPackage R) :
    ∃! j' : DPlus A ⥤ KPlus (InjectiveSubcategory A),
      plusDerivedLocalizationFunctor A ⋙ j' = P.functor ∧
        QuasiInverseOf (injectiveToDerivedFunctor (A := A)) j' := by
  sorry

/-! ## The canonical comparison of two choices -/

/- This is the objectwise comparison used in the source's final remark. -/
theorem resolution_comparison_exists_unique
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : KPlus A} {I J : KPlus (InjectiveSubcategory A)}
    (i : K ⟶ (injectiveHomotopyInclusion (A := A)).obj I)
    (i' : K ⟶ (injectiveHomotopyInclusion (A := A)).obj J)
    (hi : quasiIsoPlusProperty A i)
    (hi' : quasiIsoPlusProperty A i') :
    ∃! a : I ⟶ J,
      i ≫ (injectiveHomotopyInclusion (A := A)).map a = i' := by
  sorry

end Formalization.Books.Derived.Unit23
