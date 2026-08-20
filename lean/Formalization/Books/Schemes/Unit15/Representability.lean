import Formalization.Books.Schemes.Unit14.GlueingSchemes
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Schemes, Chapter 15: A representability criterion

This file formalizes the functor-of-points formulation of representability,
the Zariski sheaf and open-subfunctor conditions, the gluing criterion, and
the global-sections example. Yoneda and the scheme restriction API are used
for the canonical functorial constructions.
-/

namespace Formalization.Books.Schemes.Unit15

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Opposite

universe u v

noncomputable section

/-! ## Functors of points and universal families -/

/-- A set-valued contravariant functor on schemes. -/
abbrev SchemeFunctor : Type (u + 1) :=
  Scheme.{u}ᵒᵖ ⥤ Type u

/-- The functor of points `T ↦ Hom(T, X)`, namely the Yoneda functor. -/
abbrev functorOfPoints (X : Scheme.{u}) : SchemeFunctor :=
  CategoryTheory.yoneda.obj X

theorem functorOfPoints_obj (X : Scheme.{u}) (T : Scheme.{u}ᵒᵖ) :
    (functorOfPoints X).obj T = (unop T ⟶ X) := rfl

/-- Pullback of an element of a contravariant scheme functor along a morphism. -/
def pullbackElement (F : SchemeFunctor)
    {T T' : Scheme.{u}} (f : T' ⟶ T) (ξ : F.obj (op T)) : F.obj (op T') :=
  F.map f.op ξ

/-- Representability by a scheme, using Mathlib's canonical Yoneda-oriented API. -/
abbrev Representable (F : SchemeFunctor) : Prop :=
  F.IsRepresentable

/-- The source's natural-transformation form of representability. -/
theorem representable_iff_exists_yoneda_iso (F : SchemeFunctor) :
    Representable F ↔ ∃ X : Scheme.{u}, Nonempty (functorOfPoints X ≅ F) := by
  sorry

/-- Yoneda's bijection between transformations from a functor of points and
elements of the target functor. -/
def yonedaBijection (F : SchemeFunctor) (Y : Scheme.{u}) :
    (functorOfPoints Y ⟶ F) ≃ F.obj (op Y) :=
  CategoryTheory.yonedaEquiv

theorem yonedaBijection_apply (F : SchemeFunctor) (Y : Scheme.{u})
    (s : functorOfPoints Y ⟶ F) :
    yonedaBijection F Y s = s.app (op Y) (𝟙 Y) := rfl

/-- The transformation associated by Yoneda to a family `ξ`. -/
def universalFamilyTransformation (F : SchemeFunctor)
    {X : Scheme.{u}} (ξ : F.obj (op X)) : functorOfPoints X ⟶ F :=
  (yonedaBijection F X).symm ξ

theorem universalFamilyTransformation_app (F : SchemeFunctor)
    {X T : Scheme.{u}} (ξ : F.obj (op X)) (f : T ⟶ X) :
    (universalFamilyTransformation F ξ).app (op T) f = F.map f.op ξ := rfl

theorem universalFamilyTransformation_at_id (F : SchemeFunctor)
    {X : Scheme.{u}} (ξ : F.obj (op X)) :
    yonedaBijection F X (universalFamilyTransformation F ξ) = ξ := by
  exact (yonedaBijection F X).apply_symm_apply ξ

/-- A pair `(X, ξ)` represents `F` when its Yoneda transformation is an
isomorphism. -/
def Represents (F : SchemeFunctor) (X : Scheme.{u})
    (ξ : F.obj (op X)) : Prop :=
  IsIso (universalFamilyTransformation F ξ)

theorem represents_iff_representable (F : SchemeFunctor)
    {X : Scheme.{u}} {ξ : F.obj (op X)} :
    Represents F X ξ ↔ Nonempty (functorOfPoints X ≅ F) := by
  sorry

/-- A representing family gives the source's unique classifying morphism. -/
theorem represents_unique_classifying_morphism
    (F : SchemeFunctor) {X : Scheme.{u}} {ξ : F.obj (op X)}
    (hξ : Represents F X ξ) {T : Scheme.{u}} (η : F.obj (op T)) :
    ∃! f : T ⟶ X, pullbackElement F f ξ = η := by
  sorry

/-- Representing pairs are unique up to a unique isomorphism compatible with
their universal families. -/
theorem representing_pair_unique
    (F : SchemeFunctor) {X Y : Scheme.{u}}
    {ξ : F.obj (op X)} {η : F.obj (op Y)}
    (hξ : Represents F X ξ) (hη : Represents F Y η) :
    ∃! e : X ≅ Y, pullbackElement F e.hom η = ξ := by
  sorry

/-! ## The global-sections example -/

/-- The set-valued global-sections functor on schemes. -/
abbrev globalSectionsFunctor : SchemeFunctor :=
  Scheme.Γ ⋙ CategoryTheory.forget CommRingCat

/-- The universal polynomial in the global sections of the affine line. -/
noncomputable def globalSectionsUniversalElement :
    globalSectionsFunctor.obj
      (op (Spec (CommRingCat.of (Polynomial ℤ)))) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv Polynomial.X

/-- The polynomial universal property used in the affine-line example. -/
theorem polynomial_ringHom_unique (R : Type u) [CommRing R] (t : R) :
    ∃! φ : Polynomial ℤ →+* R, φ Polynomial.X = t := by
  sorry

/-- The functor of global sections is represented by the affine line over
`ℤ`, with universal section `x`. -/
theorem globalSections_represents :
    Represents globalSectionsFunctor
      (Spec (CommRingCat.of (Polynomial ℤ))) globalSectionsUniversalElement := by
  sorry

/-! ## Subfunctors, Zariski descent, and open representability -/

/-- A subfunctor `H ⊆ F`, represented objectwise by subsets stable under
pullback. -/
structure SchemeSubfunctor (F : SchemeFunctor) where
  carrier : ∀ T : Scheme.{u}, Set (F.obj (op T))
  map_mem : ∀ {T T' : Scheme.{u}} (f : T' ⟶ T) {ξ : F.obj (op T)},
    ξ ∈ carrier T → pullbackElement F f ξ ∈ carrier T'

/-- The Zariski sheaf property for a set-valued functor on schemes. -/
def SatisfiesZariskiSheafProperty (F : SchemeFunctor) : Prop :=
  ∀ (T : Scheme.{u}) {I : Type v} (U : I → T.Opens),
    IsOpenCover U →
      ∀ (ξ : ∀ i, F.obj (op (U i).toScheme)),
        (∀ i j,
          F.map (T.homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (ξ i) =
            F.map (T.homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
              (ξ j)) →
          ∃! ξT : F.obj (op T),
            ∀ i, F.map (U i).ι.op ξT = ξ i

theorem globalSections_satisfies_zariski_sheaf :
    SatisfiesZariskiSheafProperty globalSectionsFunctor := by
  sorry

/-- The open subscheme representing the locus where a family belongs to a
subfunctor. -/
def SchemeSubfunctorRepresentableByOpenImmersions
    {F : SchemeFunctor} (H : SchemeSubfunctor F) : Prop :=
  ∀ (T : Scheme.{u}) (ξ : F.obj (op T)),
    ∃ U : T.Opens, ∀ (T' : Scheme.{u}) (f : T' ⟶ T),
      (∃ g : T' ⟶ U.toScheme, g ≫ U.ι = f) ↔
        pullbackElement F f ξ ∈ H.carrier T'

/-- A scheme subfunctor represented by a scheme and a universal family. -/
def SchemeSubfunctorRepresented {F : SchemeFunctor} (H : SchemeSubfunctor F) : Prop :=
  ∃ (X : Scheme.{u}) (ξ : F.obj (op X)), ξ ∈ H.carrier X ∧
    ∀ (T : Scheme.{u}) (η : F.obj (op T)),
      η ∈ H.carrier T ↔ ∃! f : T ⟶ X, pullbackElement F f ξ = η

/-- A family of subfunctors covers `F` in the source's open-cover sense. -/
def SchemeSubfunctorsCover {F : SchemeFunctor} {I : Type v}
    (H : I → SchemeSubfunctor F) : Prop :=
  ∀ (T : Scheme.{u}) (ξ : F.obj (op T)),
    ∃ (U : I → T.Opens), IsOpenCover U ∧
      ∀ i, pullbackElement F (U i).ι ξ ∈ (H i).carrier (U i).toScheme

/-- If the subfunctors are represented by open immersions, field spectra give
the pointwise test for the covering condition. -/
theorem schemeSubfunctorsCover_of_field_spectra
    {F : SchemeFunctor} {I : Type v} (H : I → SchemeSubfunctor F)
    (hopen : ∀ i, SchemeSubfunctorRepresentableByOpenImmersions (H i))
    (hfield : ∀ (K : Type u) [Field K] (ξ : F.obj
      (op (Spec (CommRingCat.of K)))), ∃ i, ξ ∈ (H i).carrier
        (Spec (CommRingCat.of K))) :
    SchemeSubfunctorsCover H := by
  sorry

/-- The representability criterion obtained by gluing schemes representing
open subfunctors. -/
theorem glue_functors_representable
    (F : SchemeFunctor)
    (hsheaf : SatisfiesZariskiSheafProperty F)
    {I : Type v} (H : I → SchemeSubfunctor F)
    (hrepresented : ∀ i, SchemeSubfunctorRepresented (H i))
    (hopen : ∀ i, SchemeSubfunctorRepresentableByOpenImmersions (H i))
    (hcover : SchemeSubfunctorsCover H) :
    Representable F := by
  sorry

/-! ## The locally ringed space variant -/

abbrev LocallyRingedSpace :=
  Formalization.Books.Schemes.Unit02.LocallyRingedSpace

abbrev LocallyRingedSpaceFunctor : Type (u + 1) :=
  LocallyRingedSpace.{u}ᵒᵖ ⥤ Type u

/-- A subfunctor on locally ringed spaces. -/
structure LocallyRingedSpaceSubfunctor (F : LocallyRingedSpaceFunctor) where
  carrier : ∀ T : LocallyRingedSpace.{u}, Set (F.obj (op T))
  map_mem : ∀ {T T' : LocallyRingedSpace.{u}} (f : T' ⟶ T)
    {ξ : F.obj (op T)}, ξ ∈ carrier T → F.map f.op ξ ∈ carrier T'

/-- The sheaf property on the category of locally ringed spaces. -/
def SatisfiesLocallyRingedSpaceSheafProperty
    (F : LocallyRingedSpaceFunctor) : Prop :=
  ∀ (T : LocallyRingedSpace.{u}) {I : Type v} (U : I → Opens T),
    IsOpenCover U →
      ∀ (ξ : ∀ i, F.obj (op (Formalization.Books.Schemes.Unit03.openSubspace T (U i)))),
        (∀ i j,
          F.map (Formalization.Books.Schemes.Unit03.restrictHom
            (𝟙 T) (U i ⊓ U j) (U i)
            (by intro x hx; exact hx.1)).op (ξ i) =
            F.map (Formalization.Books.Schemes.Unit03.restrictHom
              (𝟙 T) (U i ⊓ U j) (U j)
              (by intro x hx; exact hx.2)).op (ξ j)) →
          ∃! ξT : F.obj (op T),
            ∀ i, F.map
                (Formalization.Books.Schemes.Unit03.openSubspaceInclusion T (U i)).op ξT =
              ξ i

/-- Open-subfunctor representability on locally ringed spaces. -/
def LocallyRingedSpaceSubfunctorRepresentableByOpenImmersions
    {F : LocallyRingedSpaceFunctor} (H : LocallyRingedSpaceSubfunctor F) : Prop :=
  ∀ (T : LocallyRingedSpace.{u}) (ξ : F.obj (op T)),
    ∃ U : Opens T, ∀ (T' : LocallyRingedSpace.{u}) (f : T' ⟶ T),
      (∃ g : T' ⟶ Formalization.Books.Schemes.Unit03.openSubspace T U,
        g ≫ Formalization.Books.Schemes.Unit03.openSubspaceInclusion T U = f) ↔
        F.map f.op ξ ∈ H.carrier T'

/-- A locally ringed space subfunctor represented by a scheme. -/
def LocallyRingedSpaceSubfunctorRepresentedByScheme
    {F : LocallyRingedSpaceFunctor} (H : LocallyRingedSpaceSubfunctor F) : Prop :=
  ∃ (X : Scheme.{u}) (ξ : F.obj (op X.toLocallyRingedSpace)),
    ξ ∈ H.carrier X.toLocallyRingedSpace ∧
      ∀ (T : LocallyRingedSpace.{u}) (η : F.obj (op T)),
        η ∈ H.carrier T ↔
          ∃! f : T ⟶ X.toLocallyRingedSpace, F.map f.op ξ = η

/-- The locally ringed space form of the source's covering condition. -/
def LocallyRingedSpaceSubfunctorsCover {F : LocallyRingedSpaceFunctor} {I : Type v}
    (H : I → LocallyRingedSpaceSubfunctor F) : Prop :=
  ∀ (T : LocallyRingedSpace.{u}) (ξ : F.obj (op T)),
    ∃ (U : I → Opens T), IsOpenCover U ∧
      ∀ i, F.map
          (Formalization.Books.Schemes.Unit03.openSubspaceInclusion T (U i)).op ξ ∈
        (H i).carrier (Formalization.Books.Schemes.Unit03.openSubspace T (U i))

/-- The locally ringed space variant of the representability criterion: the
representing object can be chosen to be a scheme. -/
theorem glue_locally_ringed_space_functors_represented_by_scheme
    (F : LocallyRingedSpaceFunctor)
    (hsheaf : SatisfiesLocallyRingedSpaceSheafProperty F)
    {I : Type v} (H : I → LocallyRingedSpaceSubfunctor F)
    (hrepresented : ∀ i, LocallyRingedSpaceSubfunctorRepresentedByScheme (H i))
    (hopen : ∀ i, LocallyRingedSpaceSubfunctorRepresentableByOpenImmersions (H i))
    (hcover : LocallyRingedSpaceSubfunctorsCover H) :
    ∃ X : Scheme.{u}, ∃ ξ : F.obj (op X.toLocallyRingedSpace),
      ∀ (T : LocallyRingedSpace.{u}) (η : F.obj (op T)),
        ∃! f : T ⟶ X.toLocallyRingedSpace, F.map f.op ξ = η := by
  sorry

end
end Formalization.Books.Schemes.Unit15
