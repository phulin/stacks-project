import Formalization.Books.Exercises.Unit32.Core

/-!
# Exercises, Chapter 32: Sheaves

The declarations below record the precise assertions in the ten numbered
exercises and the intervening remark.  Proofs are deferred to the proving
stage; the objects and hypotheses retain the source's mathematical content.
-/

namespace Formalization.Books.Exercises.Unit32

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open _root_.Topology
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit15
open Formalization.Books.Sheaves.Unit16

universe u v w

noncomputable section

/-! ## Exercises `mono-sheaves-sets`, `isomorphism-sheaves-sets`, and
`epi-sheaves-sets` -/

/-- Monomorphisms of sheaves of sets are detected by injective stalk maps. -/
theorem sheaf_mono_iff_stalk_injective
    {X : TopCat.{v}} {F G : Sh.{v, v} X} (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Function.Injective
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact Formalization.Books.Sheaves.Unit16.sheaf_mono_iff_stalk_injective φ

/-- Isomorphisms of sheaves of sets are detected by bijective stalk maps. -/
theorem sheaf_isIso_iff_stalk_bijective
    {X : TopCat.{v}} {F G : Sh.{v, v} X} (φ : F ⟶ G) :
    IsIso φ ↔ ∀ x : X, Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact Formalization.Books.Sheaves.Unit16.sheaf_isIso_iff_stalk_bijective φ

/-- Epimorphisms of sheaves of sets are detected by surjective stalk maps. -/
theorem sheaf_epi_iff_stalk_surjective
    {X : TopCat.{v}} {F G : Sh.{v, v} X} (φ : F ⟶ G) :
    Epi φ ↔ ∀ x : X, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (Type v) x).map φ.hom) := by
  exact Formalization.Books.Sheaves.Unit16.sheaf_epi_iff_stalk_surjective φ

/-! ## Exercise `adjoint-push-pull` -/

/-- Pushforward and pullback of sheaves of sets form an adjoint pair. -/
noncomputable def sheaf_pushforward_pullback_adjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheafPullback f ⊣ sheafPushforward f := by
  exact sheafPullbackPushforwardAdjunction f

/-! ## Exercise `j-shriek` -/

/-- Extension by the empty set is left adjoint to restriction for sheaves of
sets on an open subspace. -/
noncomputable def extensionByEmpty_leftAdjoint
    {X : TopCat.{v}} (U : Opens X) :
    extensionByEmpty U ⊣ restrictionToOpen U := by
  exact extensionByEmptyAdjunction U

/-- Away from an open subspace, extension by the empty set has empty stalks. -/
theorem extensionByEmpty_stalk_isEmpty
    {X : TopCat.{v}} (U : Opens X)
    (G : Sh.{v, v} (openSubspace U)) (x : X) (hx : x ∉ U) :
    IsEmpty (((extensionByEmpty U).obj G).presheaf.stalk x) := by
  sorry

/-- On the open subspace, extension by the empty set has the original stalk. -/
theorem extensionByEmpty_stalk_iso
    {X : TopCat.{v}} (U : Opens X)
    (G : Sh.{v, v} (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((extensionByEmpty U).obj G).presheaf.stalk x ≃
      G.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- Extension by zero is left adjoint to restriction for abelian sheaves. -/
noncomputable def extensionByZero_leftAdjoint
    {X : TopCat.{v}} (U : Opens X) :
    extensionByZero U ⊣ abelianRestrictionToOpen U := by
  exact extensionByZeroAdjunction U

/-- Away from an open subspace, extension by zero has the zero stalk. -/
theorem extensionByZero_stalk_zero
    {X : TopCat.{v}} (U : Opens X)
    (G : Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U))
    (x : X) (hx : x ∉ U) :
    Nonempty (((extensionByZero U).obj G).presheaf.stalk x ≅
      (⊥_ AddCommGrpCat.{v})) := by
  sorry

/-- On the open subspace, extension by zero has the original additive stalk. -/
theorem extensionByZero_stalk_iso
    {X : TopCat.{v}} (U : Opens X)
    (G : Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U))
    (x : X) (hx : x ∈ U) :
    Nonempty (((extensionByZero U).obj G).presheaf.stalk x ≅
      G.presheaf.stalk ⟨x, hx⟩) := by
  sorry

/-- The set and additive extensions have different off-open stalk
descriptions. -/
theorem extensionByEmpty_and_zero_are_distinct_constructions
    {X : TopCat.{v}} (U : Opens X)
    (G : Sh.{v, v} (openSubspace U))
    (H : Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U))
    (x : X) (hx : x ∉ U) :
    IsEmpty (((extensionByEmpty U).obj G).presheaf.stalk x) ∧
      Nonempty (((extensionByZero U).obj H).presheaf.stalk x ≅
        (⊥_ AddCommGrpCat.{v})) := by
  exact ⟨extensionByEmpty_stalk_isEmpty U G x hx,
    extensionByZero_stalk_zero U H x hx⟩

/-! ## Exercise `not-locally-generated-by-sections` -/

/-- The direct image `i_* O_Z` in the source is a skyscraper sheaf. -/
theorem realOriginDirectImage_is_skyscraper :
    IsSetSkyscraperSheaf realOriginDirectImage := by
  sorry

/-- The direct-image presentation is isomorphic to Mathlib's canonical
skyscraper representative used for the canonical stalk map below. -/
theorem realOriginDirectImage_iso_skyscraper :
    Nonempty (realOriginDirectImage ≅ realOriginSkyscraper) := by
  sorry

/-! The source names the target of the canonical map as the direct image
`i_* O_Z`.  The earlier skyscraper API uses an isomorphic canonical
representative, so we transport the map across a chosen representative
isomorphism here. -/

/-- The canonical constant-to-skyscraper map, presented with the source's
direct-image target. -/
noncomputable def realConstantToOriginDirectImage :
    realConstantZModTwo ⟶ realOriginDirectImage :=
  realConstantToOriginSkyscraper ≫
    (Classical.choice realOriginDirectImage_iso_skyscraper).inv

/-- The direct-image representative has the same surjective stalk map as the
canonical skyscraper representative. -/
theorem realConstantToOriginDirectImage_stalk_surjective :
    ∀ x : realLine, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (Type 0) x).map
        realConstantToOriginDirectImage.hom) := by
  sorry

/-- The origin skyscraper is a skyscraper sheaf. -/
theorem realOriginSkyscraper_is_skyscraper :
    IsSetSkyscraperSheaf realOriginSkyscraper := by
  exact ⟨realOrigin, ZMod 2, ⟨Iso.refl _⟩⟩

/-- The canonical map from the constant sheaf to the origin skyscraper is
surjective on every stalk. -/
theorem realConstantToOriginSkyscraper_stalk_surjective :
    ∀ x : realLine, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (Type 0) x).map
        realConstantToOriginSkyscraper.hom) := by
  sorry

/-- The canonical stalk-surjective map is an epimorphism of sheaves. -/
theorem realConstantToOriginSkyscraper_is_epi :
    Epi realConstantToOriginSkyscraper := by
  sorry

/-- The set-valued kernel is the equalizer used in the example. -/
theorem realKernel_is_equalizer :
    realKernelSheaf =
      limit (parallelPair realConstantToOriginSkyscraper
        realConstantToOriginSkyscraperZero) := rfl

/-- The additive kernel is an ideal sheaf in the constant `ZMod 2` ring
sheaf. -/
theorem realIdealSheaf_is_ideal :
    IsIdealSheafIn realRingConstantZModTwo realIdealSheaf := by
  sorry

/-- The real-line ideal sheaf is not locally generated by sections. -/
theorem realIdealSheaf_not_locally_generated :
    ¬ additiveLocallyGenerated realIdealSheaf := by
  sorry

/-! ## Exercise `quotient-j-shriek-Z` -/

/-- The direct sum of all extension-by-zero integral generators surjects onto
the given abelian sheaf. -/
theorem integerGeneratorMap_is_epi {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    Epi (integerGeneratorMap F) := by
  sorry

/-- Every abelian sheaf is a quotient of a direct sum of sheaves
`j_! (underline Z_U)`. -/
theorem every_abelian_sheaf_is_quotient_of_integer_extensions
    {X : TopCat.{v}}
    (F : Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    ∃ (I : Type v)
      (G : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X)
      (q : directSumSheafOfAbelianSheaves G ⟶ F), Epi q ∧
      ∀ i : I, ∃ U : Opens X, Nonempty (G i ≅ integerExtensionByZero U) := by
  refine ⟨integerGeneratorIndex F,
    fun i => integerExtensionByZero i.1, integerGeneratorMap F,
    integerGeneratorMap_is_epi F, ?_⟩
  intro i
  exact ⟨i.1, ⟨Iso.refl _⟩⟩

/-! ## Remark `direct-sum-stalk-abelian` -/

/-- The sheaf associated to the presheaf direct sum is canonically a sheaf
direct sum. -/
noncomputable def directSumSheafOfAbelianSheaves_is_coproduct
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) :
    IsColimit (Cofan.mk (directSumSheafOfAbelianSheaves F)
      (directSumSheafInjection F)) :=
  directSumSheaf_isColimit F

/-- Stalks commute with the direct sum of abelian sheaves. -/
theorem directSumSheafOfAbelianSheaves_stalk_iso
    {X : TopCat.{v}} {I : Type v}
    (F : I → Formalization.Books.Sheaves.Unit08.Ab.{v, v} X) (x : X) :
    Nonempty ((directSumSheafOfAbelianSheaves F).presheaf.stalk x ≅
      AddCommGrpCat.of
        (DirectSum I (fun i : I => ((F i).presheaf.stalk x : Type v)))) := by
  sorry

/-! ## Exercise `product-over-points` -/

/-- The pointwise product construction is a sheaf of abelian groups. -/
theorem productOverPointsSheaf_is_sheaf {X : TopCat.{v}}
    (A : X → AddCommGrpCat) :
    TopCat.Presheaf.IsSheaf (productOverPointsPresheaf A) := by
  exact (Formalization.Books.Sheaves.Unit09.categoryValuedSheaf_iff_isSheaf
    (F := Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf
      (F := forget AddCommGrpCat) A)).1
    (Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf_isSheaf
      (F := forget AddCommGrpCat) A)

/-- The sections of the product-over-points sheaf are pointwise products. -/
theorem productOverPointsSheaf_sections
    {X : TopCat.{v}} (A : X → AddCommGrpCat) (U : Opens X) :
    Nonempty ((productOverPointsSheaf A).presheaf.obj (op U) ≃
      ∀ x : U, A x) := by
  exact Formalization.Books.Sheaves.Unit15.pointwiseProductPresheaf_underlying_sections
    (F := forget AddCommGrpCat) A U

/-- For the constant binary family on the real line, the stalk at the origin
is not the binary fiber. -/
theorem realBooleanProductStalk_not_fiber :
    ¬ Nonempty (realBooleanProductSheaf.presheaf.stalk realOrigin ≅
      realBooleanAbelianFamily realOrigin) := by
  sorry

/-! ## Exercise `modified-product-over-points` -/

/-- The modified product is a sheaf of sets with the local section predicate
specified by the chosen basis subgroups. -/
theorem modifiedProductSetSheaf_is_sheaf
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) :
    TopCat.Presheaf.IsSheaf (modifiedProductSetSheaf D).presheaf := by
  exact (modifiedProductSetSheaf D).property

/-- The basis-local construction is a sheaf of abelian groups, as in the
source exercise. -/
theorem modifiedProductAbelianSheaf_is_sheaf
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) :
    TopCat.Presheaf.IsSheaf (modifiedProductAbelianSheaf D).presheaf := by
  exact (modifiedProductAbelianSheaf D).property

/-- The source's local section formula is represented by the predicate used to
construct the modified-product sheaf. -/
theorem modifiedProductSetSheaf_sections
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) (U : Opens X) :
    ∀ s : (modifiedProductSetSheaf D).presheaf.obj (op U),
      ∀ x : U, ∃ (V : Opens X) (hV : V ∈ D.basis)
        (hxV : x.1 ∈ V) (hVU : V ≤ U),
        (fun y : V => s.1 ⟨y, hVU y.2⟩) ∈ D.subgroup V hV := by
  sorry

/-- The same local section formula for the additive-group-valued sheaf. -/
theorem modifiedProductAbelianSheaf_sections
    {X : TopCat.{v}} {A : X → AddCommGrpCat}
    (D : ModifiedProductData A) (U : Opens X) :
    ∀ s : (modifiedProductAbelianSheaf D).presheaf.obj (op U),
      ∀ x : U, ∃ (V : Opens X) (hV : V ∈ D.basis)
        (hxV : x.1 ∈ V) (hVU : V ≤ U),
        (fun y : V => s.1 ⟨y, hVU y.2⟩) ∈ D.subgroup V hV := by
  sorry

/-- The modified-product sheaf need not have the originally chosen basis
subgroup as its sections on a basis open. -/
theorem modifiedProduct_sections_need_not_equal_basis_subgroup :
    ∃ (X : TopCat) (A : X → AddCommGrpCat) (D : ModifiedProductData A)
      (U : Opens X) (hU : U ∈ D.basis),
      (modifiedProductAbelianSheaf D).presheaf.obj (op U) ≠
        AddCommGrpCat.of (D.subgroup U hU) := by
  sorry

/-! ## Exercise `exact-but-not-a-stalk-functor` -/

/-- The source exercise asks for an exact functor on sheaves which is not a
stalk functor.  Its witness is left existential here because the source does
not specify a particular topological space or construction. -/
theorem exists_exact_functor_not_a_stalk_functor :
    ∃ (X : TopCat.{v})
      (hL : HasFiniteLimits (Sh.{v, v} X))
      (hC : HasFiniteColimits (Sh.{v, v} X))
      (F : Sh.{v, v} X ⥤ Type v),
      @IsExact (Sh.{v, v} X) _ (Type v) _ hL hC F ∧
        ¬ IsStalkFunctor F := by
  sorry

end

end Formalization.Books.Exercises.Unit32
