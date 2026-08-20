import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.Sheaf
import Formalization.Books.Derived.Unit23.ResolutionFunctors
import Formalization.Books.Homology.Unit25.DoubleComplexes
import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Formalization.Books.Sheaves.Unit25.Infrastructure

/-!
# Derived Categories, Chapter 24: functorial injective embeddings and
# resolution functors

This file formalizes the source's category of bounded-below injective
resolutions and the functorial construction from a functorial injective
embedding.  The double-complex existence statements are interfaces for the
construction; the earlier Homology chapters supply the total-complex and
double-complex resolution APIs used by those interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Derived.Unit08
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit25
open Formalization.Books.Homology.Unit27
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit22
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit24

/-! ## The category of injective resolutions -/

/- The source's `InjRes(A)` is the full subcategory of the arrow category on
   arrows between bounded-below complexes whose target is termwise injective
   and whose arrow is a quasi-isomorphism. -/
def injResObjectProperty
    {A : Type u} [Category.{v} A] [Abelian A] :
    ObjectProperty (Arrow (Comp A)) :=
  fun α =>
    IsBoundedBelow α.left ∧ IsBoundedBelow α.right ∧
      (∀ n : ℤ, Injective (α.right.X n)) ∧ QuasiIso α.hom

/-- The category of bounded-below injective resolutions in `A`. -/
abbrev InjRes
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (injResObjectProperty (A := A)).FullSubcategory

/- The source's `I` is the canonical strictly full subcategory of injective
   objects.  Keep this chapter-local name as a compatibility interface while
   reusing the established Chapter 23 construction. -/
abbrev InjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] :=
  Formalization.Books.Derived.Unit23.InjectiveSubcategory A

/- The source's `K⁺(I)` is the bounded-below homotopy category of the
   canonical full subcategory of injective objects from Chapter 23. -/
abbrev KPlusInjective
    (A : Type u) [Category.{v} A] [Abelian A] :=
  KPlus (InjectiveSubcategory A)

/-- The source functor `s : InjRes(A) ⥤ Comp⁺(A)`. -/
def injResSourceFunctor
    {A : Type u} [Category.{v} A] [Abelian A] :
    InjRes A ⥤ CompPlus A :=
  ObjectProperty.lift (boundedBelowProperty A)
    ((injResObjectProperty (A := A)).ι ⋙ Arrow.leftFunc)
    (fun R => R.property.1)

noncomputable def injResTargetComplexFunctor
    {A : Type u} [Category.{v} A] [Abelian A] :
    InjRes A ⥤ CompPlus A :=
  ObjectProperty.lift (boundedBelowProperty A)
    ((injResObjectProperty (A := A)).ι ⋙ Arrow.rightFunc)
    (fun R => R.property.2.1)

/- The source functor `t : InjRes(A) ⥤ K⁺(I)`.  Its object map lifts the
   termwise-injective right complex into the canonical injective-object
   subcategory; the corresponding morphism map is induced by the arrow
   category. -/
noncomputable def injResTargetFunctor
    {A : Type u} [Category.{v} A] [Abelian A] :
    InjRes A ⥤ KPlusInjective A := by
  let F : InjRes A ⥤ Comp A :=
    injResTargetComplexFunctor (A := A) ⋙ (boundedBelowProperty A).ι
  have hF : ∀ R : InjRes A, ∀ n : ℤ, isInjective A ((F.obj R).X n) := by
    intro R n
    change Injective (R.obj.right.X n)
    exact R.property.2.2.1 n
  let G : InjRes A ⥤ Comp (InjectiveSubcategory A) :=
    HomologicalComplex.liftFunctorObjectProperty (isInjective A) F hF
  have hG : ∀ R : InjRes A,
      boundedBelowProperty (InjectiveSubcategory A) (G.obj R) := by
    intro R
    obtain ⟨B, hB⟩ := R.property.2.1
    refine ⟨B, ?_⟩
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _
      (CategoryTheory.InjectiveObject.ι A)]
    exact hB
  let Gplus : InjRes A ⥤ CompPlus (InjectiveSubcategory A) :=
    ObjectProperty.lift (boundedBelowProperty (InjectiveSubcategory A)) G hG
  exact Gplus ⋙ HomotopyCategory.Plus.quotient (InjectiveSubcategory A)

/-! ## Resolution-functor data -/

/- The previous source section defines a resolution functor objectwise.  Reuse
   the canonical earlier-chapter package rather than introducing a second
   resolution-data structure in this chapter. -/
abbrev ResolutionFunctorData
    (A : Type u) [Category.{v} A] [Abelian A] :=
  Formalization.Books.Derived.Unit23.ResolutionFunctorData A

/-! ## Normalizing a functorial embedding -/

/- The proof in the source replaces a chosen embedding functor by the kernel
   of its map to the value at zero.  This records the resulting normalized
   choice while retaining the canonical `HasFunctorialInjectiveEmbeddings`
   interface from Homology, Chapter 27. -/
theorem functorial_injective_embedding_zero_normalization
    {A : Type u} [Category.{v} A] [Abelian A]
    (hA : HasFunctorialInjectiveEmbeddings (C := A)) :
    ∃ (J : A ⥤ Arrow A),
      J ⋙ Arrow.leftFunc = 𝟭 A ∧
        (∀ X : A, Mono (J.obj X).hom) ∧
          (∀ X : A, Injective (J.obj X).right) ∧
            IsZero (J.obj (0 : A)).right := by
  sorry

/-! ## The double-complex construction -/

/- The object appearing in the successive rows of the construction is the
   injective target chosen for a cokernel. -/
noncomputable def functorialInjectiveSuccessor
    {A : Type u} [Category.{v} A] [Abelian A]
    (J : A ⥤ Arrow A) {X Y : A} (f : X ⟶ Y) : A :=
  (J.obj (cokernel f)).right

/- A double complex produced by the source construction, together with all
   hypotheses needed by the earlier double-complex resolution theorem. -/
structure FunctorialInjectiveDoubleComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : CompPlus A) (J : A ⥤ Arrow A) where
  /-- The double complex `I^{p,q}`. -/
  doubleComplex : DoubleComplex A
  /-- Its augmentation is a double-complex resolution of `K`. -/
  resolution : DoubleComplexResolutionHypotheses K.obj doubleComplex
  /-- Every entry is injective. -/
  entryInjective : ∀ p q : ℤ, Injective (doubleComplex.obj p q)
  /-- All entries vanish below the lower bound of `K`. -/
  zeroBelow : ∃ B : ℤ, ∀ p q : ℤ, p < B → IsZero (doubleComplex.obj p q)
  /-- The first row is the chosen injective embedding of each term. -/
  degreeZeroObject : ∀ p : ℤ,
    doubleComplex.obj p 0 = (J.obj (K.obj.X p)).right
  /-- The source term is identified with the left endpoint of the chosen
      embedding. -/
  degreeZeroSource : ∀ p : ℤ,
    K.obj.X p = (J.obj (K.obj.X p)).left
  /-- After identifying the first row with the chosen target, the
      augmentation is the chosen embedding. -/
  degreeZeroMap : ∀ p : ℤ,
    resolution.augmentation.f p ≫
        eqToHom (degreeZeroObject p) =
      eqToHom (degreeZeroSource p) ≫ (J.obj (K.obj.X p)).hom
  /-- The first-row augmentation is monomorphic, as is the chosen embedding. -/
  degreeZeroMapMono : ∀ p : ℤ, Mono (resolution.augmentation.f p)
  /-- The first successive row is the injective target of the cokernel of the
      augmentation `Kᵖ ⟶ I^{p,0}`. -/
  degreeOneObject : ∀ p : ℤ,
    doubleComplex.obj p 1 =
      functorialInjectiveSuccessor J (resolution.augmentation.f p)
  /-- Each later row is the injective target of the successive cokernel. -/
  successiveObject : ∀ (p r : ℤ), 0 ≤ r →
    doubleComplex.obj p (r + 2) =
      functorialInjectiveSuccessor J (doubleComplex.d2 p r)

/- The source's explicit `q < 0` convention and its consequences are exposed
   separately from the stronger resolution package. -/
theorem functorialInjectiveDoubleComplex_zero_below
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J) :
    ∃ B : ℤ, ∀ p q : ℤ, p < B → IsZero (D.doubleComplex.obj p q) := by
  exact D.zeroBelow

theorem functorialInjectiveDoubleComplex_entries_injective
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J) :
    ∀ p q : ℤ, Injective (D.doubleComplex.obj p q) := by
  exact D.entryInjective

theorem functorialInjectiveDoubleComplex_negative_rows_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J) :
    ∀ p q : ℤ, q < 0 → IsZero (D.doubleComplex.obj p q) := by
  exact D.resolution.supported

theorem functorialInjectiveDoubleComplex_kernel_iso
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J) :
    ∀ p : ℤ, ∃ e : K.obj.X p ≅ kernel (D.doubleComplex.d2 p 0),
      e.hom ≫ kernel.ι (D.doubleComplex.d2 p 0) =
        D.resolution.augmentation.f p := by
  exact D.resolution.augmentation_kernel_iso

/- The construction uses the normalized choice and is functorial in maps of
   bounded-below complexes. -/
theorem functorial_injective_double_complex_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {J : A ⥤ Arrow A}
    (hJ : J ⋙ Arrow.leftFunc = 𝟭 A ∧
      (∀ X : A, Mono (J.obj X).hom) ∧
        (∀ X : A, Injective (J.obj X).right) ∧
          IsZero (J.obj (0 : A)).right)
    (K : CompPlus A) :
    Nonempty (FunctorialInjectiveDoubleComplex K J) := by
  sorry

theorem functorial_injective_double_complex_is_functorial
    {A : Type u} [Category.{v} A] [Abelian A]
    {J : A ⥤ Arrow A}
    (hJ : J ⋙ Arrow.leftFunc = 𝟭 A ∧
      (∀ X : A, Mono (J.obj X).hom) ∧
        (∀ X : A, Injective (J.obj X).right) ∧
          IsZero (J.obj (0 : A)).right) :
    ∃ inj : CompPlus A ⥤ InjRes A,
      inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A) := by
  sorry

/- The earlier Homology interface supplies the totalization and the
   quasi-isomorphism from the augmented complex. -/
theorem functorial_double_complex_totalization_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J) :
    Nonempty (TotalComplexPresentation D.doubleComplex) :=
  doubleComplex_resolution_totalization_exists D.resolution

theorem functorial_double_complex_totalization_quasiIso
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J)
    (T : TotalComplexPresentation D.doubleComplex) :
    QuasiIso (doubleComplexResolutionMap T D.resolution) :=
  doubleComplex_gives_resolution T D.resolution

theorem functorial_double_complex_totalization_is_resolution
    {A : Type u} [Category.{v} A] [Abelian A]
    {K : CompPlus A} {J : A ⥤ Arrow A}
    (D : FunctorialInjectiveDoubleComplex K J)
    (T : TotalComplexPresentation D.doubleComplex) :
    IsBoundedBelow T.complex ∧
      (∀ n : ℤ, Injective (T.complex.X n)) ∧
      QuasiIso (doubleComplexResolutionMap T D.resolution) := by
  sorry

/-! ## The functorial-resolution lemma -/

/-- Functorial injective embeddings produce a functorial bounded-below
injective resolution of every bounded-below complex. -/
theorem functorial_injective_resolution_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    (hA : HasFunctorialInjectiveEmbeddings (C := A)) :
    ∃ inj : CompPlus A ⥤ InjRes A,
      inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A) := by
  obtain ⟨J, hJ₀, hJmono, hJinj, hJzero⟩ :=
    functorial_injective_embedding_zero_normalization hA
  exact functorial_injective_double_complex_is_functorial
    ⟨hJ₀, hJmono, hJinj, hJzero⟩

/-- Any functorial choice of objects of `InjRes(A)` over the identity source
functor supplies the source's resolution-functor data. -/
theorem resolutionFunctorData_exists_of_inj
    {A : Type u} [Category.{v} A] [Abelian A]
    (inj : CompPlus A ⥤ InjRes A)
    (hsource : inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A)) :
    Nonempty (ResolutionFunctorData A) := by
  sorry

/-! ## Matching the induced homotopy functor -/

/- The square in the source is the arrow-category commutativity condition on
   the image of a map under `inj`. -/
def injMapSquareCondition
    {A : Type u} [Category.{v} A] [Abelian A]
    (inj : CompPlus A ⥤ InjRes A) {K L : CompPlus A}
    (α : K ⟶ L) : Prop :=
  (inj.map α).hom.left ≫ (inj.obj L).obj.hom =
    (inj.obj K).obj.hom ≫ (inj.map α).hom.right

theorem inj_map_square_commutes
    {A : Type u} [Category.{v} A] [Abelian A]
    (inj : CompPlus A ⥤ InjRes A) {K L : CompPlus A}
    (α : K ⟶ L) :
    injMapSquareCondition inj α := by
  exact (inj.map α).hom.w

/- The resolution data from the preceding definition can be upgraded to a
   functor on the bounded-below homotopy category; the comparison square is
   the `2`-commutative square in the source. -/
structure ResolutionFunctorCompatibility
    {A : Type u} [Category.{v} A] [Abelian A]
    (inj : CompPlus A ⥤ InjRes A) where
  sourceIdentity : inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A)
  j : KPlus A ⥤ KPlusInjective A
  /-- The objectwise comparison from `j` to the target selected by `inj`. -/
  comparisonIso : ∀ K : CompPlus A,
    j.obj ((HomotopyCategory.Plus.quotient A).obj K) ≅
      (injResTargetFunctor (A := A)).obj (inj.obj K)
  /-- The comparison is natural and sends `j(α)` to `inj(α)` up to homotopy. -/
  comparisonNaturality : ∀ {K L : CompPlus A} (α : K ⟶ L),
    j.map ((HomotopyCategory.Plus.quotient A).map α) ≫
        (comparisonIso L).hom =
      (comparisonIso K).hom ≫
        (injResTargetFunctor (A := A)).map (inj.map α)

theorem resolutionFunctorCompatibility_exists
    {A : Type u} [Category.{v} A] [Abelian A]
    (inj : CompPlus A ⥤ InjRes A)
    (hsource : inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A)) :
    Nonempty (ResolutionFunctorCompatibility inj) := by
  sorry

/-! ## Big abelian categories and the stated examples -/

/- The concrete module and sheaf examples are already provided by the
   earlier injective-development chapters; these statements expose the
   chapter's applications using that established predicate directly. -/
theorem moduleCat_supports_functorial_resolution
    (R : Type u) [CommRing R] :
    HasFunctorialInjectiveEmbeddings (C := ModuleCat.{u} R) := by
  sorry

theorem presheafOfModules_supports_functorial_resolution
    {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) :
    HasFunctorialInjectiveEmbeddings
      (C := PresheafOfModules.{u} R) := by
  sorry

theorem sheafOfModules_supports_functorial_resolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    HasFunctorialInjectiveEmbeddings
      (C := SheafOfModules.{u} R) := by
  sorry

theorem ringedSpaceModuleCat_supports_functorial_resolution
    (X : RingedSpace.{u}) :
    HasFunctorialInjectiveEmbeddings
      (C := Mod X.structureSheaf) := by
  sorry

end Formalization.Books.Derived.Unit24
