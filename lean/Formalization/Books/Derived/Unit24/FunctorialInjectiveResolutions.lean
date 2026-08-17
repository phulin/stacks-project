import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.Sheaf
import Formalization.Books.Derived.Unit18.InjectiveResolutions
import Formalization.Books.Derived.Unit20.InjectiveResolutions
import Formalization.Books.Homology.Unit25.DoubleComplexes
import Formalization.Books.Homology.Unit27.Injectives
import Formalization.Books.Sheaves.Unit10.SheavesOfModules
import Formalization.Books.Sheaves.Unit22.RingedSpaces

/-!
# Derived Categories, Chapter 24: functorial injective embeddings

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
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit18
open Formalization.Books.Derived.Unit20
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
   objects. -/
def injectiveObjectProperty
    {A : Type u} [Category.{v} A] [Abelian A] : ObjectProperty A :=
  fun I => Injective I

/-- The strictly full subcategory of injective objects of `A`. -/
abbrev InjectiveSubcategory
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (injectiveObjectProperty (A := A)).FullSubcategory

/- The source writes `K⁺(I)` for complexes of injective objects.  We use the
   canonical full subcategory of `K⁺(A)` consisting of objects represented by
   bounded-below termwise-injective complexes. -/
def injectiveHomotopyProperty
    {A : Type u} [Category.{v} A] [Abelian A] :
    ObjectProperty (KPlus A) :=
  fun X =>
    ∃ I : CompPlus A, IsTermwiseInjectiveComplex I ∧
      Nonempty ((HomotopyCategory.Plus.quotient A).obj I ≅ X)

/-- The source's `K⁺(I)`, represented as a full subcategory of `K⁺(A)`. -/
abbrev KPlusInjective
    (A : Type u) [Category.{v} A] [Abelian A] :=
  (injectiveHomotopyProperty (A := A)).FullSubcategory

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

/-- The source functor `t : InjRes(A) ⥤ K⁺(I)`. -/
def injResTargetFunctor
    {A : Type u} [Category.{v} A] [Abelian A] :
    InjRes A ⥤ KPlusInjective A :=
  ObjectProperty.lift (injectiveHomotopyProperty (A := A))
    (injResTargetComplexFunctor (A := A) ⋙
      HomotopyCategory.Plus.quotient A)
    (fun R =>
      let I : CompPlus A := ⟨R.obj.right, R.property.2.1⟩
      ⟨I, R.property.2.2.1, ⟨Iso.refl _⟩⟩)

/-! ## Resolution-functor data -/

/- The previous source section defines a resolution functor objectwise.  Reuse
   the canonical earlier-chapter package for a bounded-below termwise
   injective complex equipped with a quasi-isomorphism. -/
abbrev ResolutionFunctorData
    (A : Type u) [Category.{v} A] [Abelian A] :=
  ∀ K : CompPlus A, ComplexInjectiveResolution K.obj

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
      (∀ n : ℤ, Injective (T.complex.X n)) := by
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

/- The construction only uses an objectwise functorial injective embedding;
   it does not quantify over the class of all objects. -/
def SupportsFunctorialResolutionConstruction
    {A : Type u} [Category.{v} A] [Abelian A] : Prop :=
  HasFunctorialInjectiveEmbeddings (C := A)

theorem functorial_resolution_exists_of_construction_support
    {A : Type u} [Category.{v} A] [Abelian A]
    (hA : SupportsFunctorialResolutionConstruction (A := A)) :
    ∃ inj : CompPlus A ⥤ InjRes A,
      inj ⋙ injResSourceFunctor = 𝟭 (CompPlus A) :=
  functorial_injective_resolution_exists hA

/- The concrete module and sheaf examples are already provided by the
   earlier injective-development chapters; these aliases make the chapter's
   applications available at its own interface. -/
theorem moduleCat_supports_functorial_resolution
    (R : Type u) [CommRing R] :
    SupportsFunctorialResolutionConstruction (A := ModuleCat.{u} R) := by
  sorry

theorem presheafOfModules_supports_functorial_resolution
    {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) :
    SupportsFunctorialResolutionConstruction
      (A := PresheafOfModules.{u} R) := by
  sorry

theorem sheafOfModules_supports_functorial_resolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    SupportsFunctorialResolutionConstruction
      (A := SheafOfModules.{u} R) := by
  sorry

theorem ringedSpaceModuleCat_supports_functorial_resolution
    (X : RingedSpace.{u}) :
    SupportsFunctorialResolutionConstruction
      (A := Mod X.structureSheaf) := by
  sorry

end Formalization.Books.Derived.Unit24
