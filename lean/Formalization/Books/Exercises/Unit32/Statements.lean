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

/-! The introductory categorical definitions are already the canonical
`Mono`, `IsIso`, and `Epi` predicates.  Their set-valued characterizations
are built into the standard `Type` category API and are used by the
stalkwise criteria below, so no parallel definitions are introduced here. -/

/-- In the category of sets, monomorphisms are injective functions. -/
theorem type_mono_iff_injective {α β : Type v} (f : α → β) :
    Mono (TypeCat.ofHom f) ↔ Function.Injective f := by
  simpa using (mono_iff_injective (TypeCat.ofHom f))

/-- In the category of sets, isomorphisms are bijective functions. -/
theorem type_isIso_iff_bijective {α β : Type v} (f : α → β) :
    IsIso (TypeCat.ofHom f) ↔ Function.Bijective f := by
  simpa using (isIso_iff_bijective (TypeCat.ofHom f))

/-- In the category of sets, epimorphisms are surjective functions. -/
theorem type_epi_iff_surjective {α β : Type v} (f : α → β) :
    Epi (TypeCat.ofHom f) ↔ Function.Surjective f := by
  simpa using (epi_iff_surjective (TypeCat.ofHom f))

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
  exact Formalization.Books.Sheaves.Unit22.openSetSheafExtension_stalk_empty U G x hx

/-- On the open subspace, extension by the empty set has the original stalk. -/
theorem extensionByEmpty_stalk_iso
    {X : TopCat.{v}} (U : Opens X)
    (G : Sh.{v, v} (openSubspace U)) (x : X) (hx : x ∈ U) :
    Nonempty (((extensionByEmpty U).obj G).presheaf.stalk x ≃
      G.presheaf.stalk ⟨x, hx⟩) := by
  exact Formalization.Books.Sheaves.Unit22.openSetSheafExtension_stalk_iso U G x hx

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
  exact Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_stalk_initial
    AddCommGrpCat U G x hx

/-- On the open subspace, extension by zero has the original additive stalk. -/
theorem extensionByZero_stalk_iso
    {X : TopCat.{v}} (U : Opens X)
    (G : Formalization.Books.Sheaves.Unit08.Ab.{v, v} (openSubspace U))
    (x : X) (hx : x ∈ U) :
    Nonempty (((extensionByZero U).obj G).presheaf.stalk x ≅
      G.presheaf.stalk ⟨x, hx⟩) := by
  exact Formalization.Books.Sheaves.Unit22.openAlgebraicSheafExtension_stalk_iso
    AddCommGrpCat U G x hx

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

private noncomputable instance realOriginMembershipDecidable (U : Opens realLine) :
    Decidable (realOrigin ∈ U) := Classical.propDecidable _

private lemma type_eqToHom_concrete_apply {α β : Type v} (h : α = β) (x : α) :
    (ConcreteCategory.hom (eqToHom h)) x = cast h x := by
  cases h
  rfl

private lemma type_cast_trans {α β γ : Type v} (h : α = β) (k : β = γ) (x : α) :
    cast k (cast h x) = cast (h.trans k) x := by
  cases h
  cases k
  rfl

private noncomputable def realOriginDirectImage_origin_equiv_at
    (U : Opens realLine) (hU : realOrigin ∈ U) :
    ((realOriginDirectImage.presheaf.obj (op U)) : Type 0) ≃ ZMod 2 := by
  classical
  let V : Opens realOriginSubspace :=
    (Opens.map realOriginSubspaceInclusion).obj U
  let p : V := ⟨⟨realOrigin, rfl⟩, by
    change realOriginSubspaceInclusion ⟨realOrigin, rfl⟩ ∈ U
    simpa [realOriginSubspaceInclusion] using hU⟩
  letI : Subsingleton V := ⟨fun a b => by
    apply Subtype.ext
    apply Subtype.ext
    exact a.1.2.trans b.1.2.symm⟩
  let : TopologicalSpace (ZMod 2) := ⊥
  let : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  exact
    { toFun := fun s => (ConcreteCategory.hom s) p
      invFun := fun a => TopCat.ofHom
        { toFun := fun _ => a
          continuous_toFun :=
            (continuous_iff_locallyConstant_of_discrete (fun _ : V => a)).mpr
              (IsLocallyConstant.const a) }
      left_inv := by
        intro s
        apply TopCat.Hom.ext
        apply ContinuousMap.ext
        intro y
        change (ConcreteCategory.hom s) p = (ConcreteCategory.hom s) y
        simpa [Subsingleton.elim y p]
      right_inv := by
        intro a
        rfl }

private noncomputable def realOriginDirectImage_origin_equiv_away
    (U : Opens realLine) (hU : realOrigin ∉ U) :
    ((realOriginDirectImage.presheaf.obj (op U)) : Type 0) ≃ (⊤_ Type 0) := by
  classical
  let V : Opens realOriginSubspace :=
    (Opens.map realOriginSubspaceInclusion).obj U
  have hVempty : ∀ y : V, False := by
    intro y
    apply hU
    have hy : realOriginSubspaceInclusion y.1 ∈ U := by
      change realOriginSubspaceInclusion y.1 ∈ U
      exact y.2
    have hy0 : realOriginSubspaceInclusion y.1 = realOrigin := by
      exact y.1.2
    rwa [← hy0]
  let : TopologicalSpace (ZMod 2) := ⊥
  let : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  exact
    { toFun := fun _ => default
      invFun := fun _ => TopCat.ofHom
        { toFun := fun y => False.elim (hVempty y)
          continuous_toFun := by
            apply (continuous_iff_locallyConstant_of_discrete _).mpr
            exact IsLocallyConstant.of_constant _ (fun x y =>
              False.elim (hVempty x)) }
      left_inv := by
        intro s
        apply TopCat.Hom.ext
        apply ContinuousMap.ext
        intro y
        exact False.elim (hVempty y)
      right_inv := by
        intro a
        exact Subsingleton.elim _ _ }

private noncomputable def realOriginDirectImage_origin_equiv (U : Opens realLine) :
    ((realOriginDirectImage.presheaf.obj (op U)) : Type 0) ≃
      if realOrigin ∈ U then ZMod 2 else (⊤_ Type 0) := by
  classical
  by_cases hU : realOrigin ∈ U
  · simpa only [if_pos hU] using
      (realOriginDirectImage_origin_equiv_at U hU)
  · simpa only [if_neg hU] using
      (realOriginDirectImage_origin_equiv_away U hU)

private noncomputable def realOriginSkyscraper_obj_eq_at
    (U : Opens realLine) (hU : realOrigin ∈ U) :
    (realOriginSkyscraper.presheaf.obj (op U) : Type 0) = ZMod 2 := by
  dsimp [realOriginSkyscraper, skyscraperSheaf, skyscraperPresheaf]
  exact if_pos hU

private noncomputable def realOriginSkyscraper_obj_eq_away
    (U : Opens realLine) (hU : realOrigin ∉ U) :
    (realOriginSkyscraper.presheaf.obj (op U) : Type 0) = (⊤_ Type 0) := by
  dsimp [realOriginSkyscraper, skyscraperSheaf, skyscraperPresheaf]
  exact if_neg hU

private noncomputable def realOriginDirectImage_component_iso (U : Opens realLine) :
    realOriginDirectImage.presheaf.obj (op U) ≅
      realOriginSkyscraper.presheaf.obj (op U) := by
  classical
  by_cases hU : realOrigin ∈ U
  · let e : realOriginDirectImage.presheaf.obj (op U) ≅ ZMod 2 :=
      { hom := TypeCat.ofHom (realOriginDirectImage_origin_equiv_at U hU)
        inv := TypeCat.ofHom (realOriginDirectImage_origin_equiv_at U hU).symm
        hom_inv_id := by
          ext x
          exact (realOriginDirectImage_origin_equiv_at U hU).left_inv x
        inv_hom_id := by
          ext x
          exact (realOriginDirectImage_origin_equiv_at U hU).right_inv x }
    exact e ≪≫ eqToIso (realOriginSkyscraper_obj_eq_at U hU).symm
  · let e : realOriginDirectImage.presheaf.obj (op U) ≅ (⊤_ Type 0) :=
      { hom := TypeCat.ofHom (realOriginDirectImage_origin_equiv_away U hU)
        inv := TypeCat.ofHom (realOriginDirectImage_origin_equiv_away U hU).symm
        hom_inv_id := by
          ext x <;> exact (realOriginDirectImage_origin_equiv_away U hU).left_inv x
        inv_hom_id := by
          ext x <;> exact (realOriginDirectImage_origin_equiv_away U hU).right_inv x }
    exact e ≪≫ eqToIso (realOriginSkyscraper_obj_eq_away U hU).symm

private lemma realOriginDirectImage_origin_equiv_at_map
    (U V : Opens realLine) (hVU : V ≤ U)
    (hU : realOrigin ∈ U) (hV : realOrigin ∈ V)
    (s : realOriginDirectImage.presheaf.obj (op U)) :
    realOriginDirectImage_origin_equiv_at V hV
        (realOriginDirectImage.presheaf.map (homOfLE hVU).op s) =
      realOriginDirectImage_origin_equiv_at U hU s := by
  classical
  dsimp [realOriginDirectImage_origin_equiv_at, realOriginDirectImage,
    realOriginSubspaceConstantZModTwo,
    Formalization.Books.Sheaves.Unit07.constantSheaf,
    TopCat.Presheaf.pushforward, TopCat.Presheaf.restrict]
  rfl

private noncomputable def realOriginDirectImage_presheaf_hom :
    realOriginDirectImage.presheaf ⟶ realOriginSkyscraper.presheaf :=
  { app := fun U => (realOriginDirectImage_component_iso U.unop).hom
    naturality := by
      intro U V f
      ext s
      by_cases hV : realOrigin ∈ V.unop
      · have hU : realOrigin ∈ U.unop := leOfHom f.unop hV
        let hUobj :
            ((skyscraperPresheaf realOrigin (ZMod 2)).obj U : Type 0) = ZMod 2 := by
          simp only [skyscraperPresheaf_obj, unop_op]
          exact if_pos hU
        let hVobj :
            ((skyscraperPresheaf realOrigin (ZMod 2)).obj V : Type 0) = ZMod 2 := by
          simp only [skyscraperPresheaf_obj, unop_op]
          exact if_pos hV
        have hmap :
            eqToHom hUobj.symm ≫
                (skyscraperPresheaf realOrigin (ZMod 2)).map
                  f =
              eqToHom hVobj.symm := by
          rw [skyscraperPresheaf_map, dif_pos hV]
          exact eqToHom_trans _ _
        have hUcomp :
            (realOriginDirectImage_component_iso U.unop).hom =
              TypeCat.ofHom (realOriginDirectImage_origin_equiv_at U.unop hU) ≫
                eqToHom hUobj.symm := by
          dsimp [realOriginDirectImage_component_iso]
          simp only [dif_pos hU]
          rfl
        have hVcomp :
            (realOriginDirectImage_component_iso V.unop).hom =
              TypeCat.ofHom (realOriginDirectImage_origin_equiv_at V.unop hV) ≫
                eqToHom hVobj.symm := by
          dsimp [realOriginDirectImage_component_iso]
          simp only [dif_pos hV]
          rfl
        rw [hVcomp, hUcomp]
        change
          (ConcreteCategory.hom
            ((realOriginDirectImage.presheaf.map f) ≫
              (TypeCat.ofHom (realOriginDirectImage_origin_equiv_at V.unop hV) ≫
                eqToHom hVobj.symm))) s =
            (ConcreteCategory.hom
              ((TypeCat.ofHom (realOriginDirectImage_origin_equiv_at U.unop hU) ≫
                eqToHom hUobj.symm) ≫
                (skyscraperPresheaf realOrigin (ZMod 2)).map f)) s
        simp only [Category.assoc]
        rw [hmap]
        simp only [ConcreteCategory.comp_apply, type_eqToHom_concrete_apply]
        have hsource :
            realOriginDirectImage_origin_equiv_at V.unop hV
                (realOriginDirectImage.presheaf.map f s) =
              realOriginDirectImage_origin_equiv_at U.unop hU s := by
          have hf : f = (homOfLE f.unop.le).op := Subsingleton.elim _ _
          rw [hf]
          exact realOriginDirectImage_origin_equiv_at_map
            U.unop V.unop f.unop.le hU hV s
        exact congrArg (fun z => cast hVobj.symm z)
          hsource
      · dsimp [realOriginDirectImage_component_iso,
          realOriginSkyscraper, skyscraperSheaf, skyscraperPresheaf]
        split_ifs with h
        · exact (hV h).elim
        · letI : Subsingleton
              (if realOrigin ∈ V.unop then ZMod 2 else (⊤_ Type 0)) := by
            rw [if_neg h]
            infer_instance
          apply Subsingleton.elim }

private noncomputable def realOriginDirectImage_presheaf_iso :
    realOriginDirectImage.presheaf ≅ realOriginSkyscraper.presheaf := by
  classical
  let hom := realOriginDirectImage_presheaf_hom
  let inv : realOriginSkyscraper.presheaf ⟶ realOriginDirectImage.presheaf :=
    { app := fun U => (realOriginDirectImage_component_iso U.unop).inv
      naturality := by
        intro U V f
        apply (cancel_mono (realOriginDirectImage_component_iso V.unop).hom).1
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        change realOriginSkyscraper.presheaf.map f =
          (realOriginDirectImage_component_iso U.unop).inv ≫
            realOriginDirectImage.presheaf.map f ≫
              realOriginDirectImage_presheaf_hom.app V
        rw [realOriginDirectImage_presheaf_hom.naturality f]
        dsimp [realOriginDirectImage_presheaf_hom]
        simp }
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply NatTrans.ext
        funext U
        exact (realOriginDirectImage_component_iso U.unop).hom_inv_id
      inv_hom_id := by
        apply NatTrans.ext
        funext U
        exact (realOriginDirectImage_component_iso U.unop).inv_hom_id }

/-- The direct image `i_* O_Z` in the source is a skyscraper sheaf. -/
theorem realOriginDirectImage_is_skyscraper :
    IsSetSkyscraperSheaf realOriginDirectImage := by
  classical
  refine ⟨realOrigin, ZMod 2, ?_⟩
  exact ⟨ObjectProperty.isoMk
    (P := fun F : TopCat.Presheaf (Type 0) realLine =>
      TopCat.Presheaf.IsSheaf F)
    (X := realOriginDirectImage) (Y := realOriginSkyscraper)
    realOriginDirectImage_presheaf_iso⟩

/-- The direct-image presentation is isomorphic to Mathlib's canonical
skyscraper representative used for the canonical stalk map below. -/
theorem realOriginDirectImage_iso_skyscraper :
    Nonempty (realOriginDirectImage ≅ realOriginSkyscraper) := by
  classical
  exact ⟨ObjectProperty.isoMk
    (P := fun F : TopCat.Presheaf (Type 0) realLine =>
      TopCat.Presheaf.IsSheaf F)
    (X := realOriginDirectImage) (Y := realOriginSkyscraper)
    realOriginDirectImage_presheaf_iso⟩

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
  classical
  have hcanon : ∀ y : realLine, Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (Type 0) y).map
        realConstantToOriginSkyscraper.hom) := by
    intro y
    by_cases hy : y = realOrigin
    · subst y
      let g :
          realConstantZModTwo ⟶ (skyscraperSheafFunctor realOrigin).obj (ZMod 2) :=
        by simpa [realOriginSkyscraper, skyscraperSheafFunctor] using
          realConstantToOriginSkyscraper
      have hcomp :=
        (stalkSkyscraperSheafAdjunction realOrigin).homEquiv_counit
          (C := TopCat.Sheaf (Type 0) realLine) (D := Type 0)
          realConstantZModTwo (ZMod 2) g
      have hmap :
          TypeCat.ofHom realConstantZModTwoStalkMap =
            ((TopCat.Sheaf.forget (Type 0) realLine ⋙
              TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g) ≫
              (stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2) := by
        rw [← hcomp]
        dsimp [g, realConstantToOriginSkyscraper, realOriginSkyscraper,
          skyscraperSheafFunctor]
        exact (Equiv.apply_symm_apply _ _).symm
      have hfun :
          realConstantZModTwoStalkMap =
            (ConcreteCategory.hom
                ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2))) ∘
              (ConcreteCategory.hom
                ((TopCat.Sheaf.forget (Type 0) realLine ⋙
                  TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) := by
        funext z
        change ((TopCat.Sheaf.forget (Type 0) realLine ⋙
            TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).obj
            realConstantZModTwo) at z
        have hz := ConcreteCategory.congr_hom hmap z
        change realConstantZModTwoStalkMap z =
          (((TopCat.Sheaf.forget (Type 0) realLine ⋙
            TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g ≫
            (stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2)) z) at hz
        rw [CategoryTheory.comp_apply] at hz
        exact hz
      have hc : Function.Injective
          (ConcreteCategory.hom
            ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2))) := by
        change Function.Injective (ConcreteCategory.hom
          ((skyscraperPresheafStalkOfSpecializes realOrigin (ZMod 2)
            specializes_rfl).hom))
        exact ((type_isIso_iff_bijective _).mp (by infer_instance)).1
      have hsurj :
          Function.Surjective
            (ConcreteCategory.hom
                ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2)) ∘
              ConcreteCategory.hom
                ((TopCat.Sheaf.forget (Type 0) realLine ⋙
                  TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) := by
        rw [← hfun]
        exact (constantSheafStalkEquiv (X := realLine) (ZMod 2) realOrigin).symm.surjective
      have hfg : Function.Surjective
          (ConcreteCategory.hom
            ((TopCat.Sheaf.forget (Type 0) realLine ⋙
              TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) :=
        hsurj.of_comp_left hc
      dsimp [g, realConstantToOriginSkyscraper, realOriginSkyscraper,
        skyscraperSheafFunctor] at hfg ⊢
      exact hfg
    · have hspec : ¬ realOrigin ⤳ y := by
        intro h
        exact hy ((specializes_iff_eq (x := realOrigin) (y := y)).mp h).symm
      let e := skyscraperPresheafStalkOfNotSpecializes realOrigin (ZMod 2) hspec
      have he : Function.Injective (ConcreteCategory.hom e.hom) :=
        ((type_isIso_iff_bijective _).mp (by infer_instance)).1
      intro z
      refine ⟨(constantSheafStalkEquiv (X := realLine) (ZMod 2) y) (0 : ZMod 2), ?_⟩
      apply he
      exact Subsingleton.elim _ _
  intro x
  let e := Classical.choice realOriginDirectImage_iso_skyscraper
  letI : IsIso e.inv := by infer_instance
  have hbij : Function.Bijective
      ((TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom) :=
    (sheaf_isIso_iff_stalk_bijective e.inv).mp (by infer_instance) x
  have hcomp :
      (TopCat.Presheaf.stalkFunctor (Type 0) x).map
          realConstantToOriginDirectImage.hom =
        (TopCat.Presheaf.stalkFunctor (Type 0) x).map
          realConstantToOriginSkyscraper.hom ≫
          (TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom := by
    change (TopCat.Presheaf.stalkFunctor (Type 0) x).map
        (realConstantToOriginSkyscraper.hom ≫ e.inv.hom) = _
    rw [Functor.map_comp]
  rw [hcomp]
  have hfun :
      ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor (Type 0) x).map
            realConstantToOriginSkyscraper.hom ≫
            (TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom) =
        (ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom)) ∘
          ConcreteCategory.hom
            ((TopCat.Presheaf.stalkFunctor (Type 0) x).map
              realConstantToOriginSkyscraper.hom) := by
    funext z
    change (ConcreteCategory.hom
        (((TopCat.Presheaf.stalkFunctor (Type 0) x).map
          realConstantToOriginSkyscraper.hom) ≫
          (TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom)) z =
      (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor (Type 0) x).map e.inv.hom))
        ((ConcreteCategory.hom
          ((TopCat.Presheaf.stalkFunctor (Type 0) x).map
            realConstantToOriginSkyscraper.hom)) z)
    rw [CategoryTheory.comp_apply]
  rw [hfun]
  exact hbij.2.comp (hcanon x)

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
  classical
  intro x
  by_cases hx : x = realOrigin
  · subst x
    let g :
        realConstantZModTwo ⟶ (skyscraperSheafFunctor realOrigin).obj (ZMod 2) :=
      by simpa [realOriginSkyscraper, skyscraperSheafFunctor] using
        realConstantToOriginSkyscraper
    have hcomp :=
      (stalkSkyscraperSheafAdjunction realOrigin).homEquiv_counit
        (C := TopCat.Sheaf (Type 0) realLine) (D := Type 0)
        realConstantZModTwo (ZMod 2) g
    have hmap :
        TypeCat.ofHom realConstantZModTwoStalkMap =
          ((TopCat.Sheaf.forget (Type 0) realLine ⋙
            TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g) ≫
            (stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2) := by
      rw [← hcomp]
      dsimp [g, realConstantToOriginSkyscraper, realOriginSkyscraper,
        skyscraperSheafFunctor]
      exact (Equiv.apply_symm_apply _ _).symm
    have hfun :
        realConstantZModTwoStalkMap =
          (ConcreteCategory.hom
              ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2))) ∘
            (ConcreteCategory.hom
              ((TopCat.Sheaf.forget (Type 0) realLine ⋙
                TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) := by
      funext z
      change ((TopCat.Sheaf.forget (Type 0) realLine ⋙
          TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).obj
          realConstantZModTwo) at z
      have hz := ConcreteCategory.congr_hom hmap z
      change realConstantZModTwoStalkMap z =
        (((TopCat.Sheaf.forget (Type 0) realLine ⋙
          TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g ≫
          (stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2)) z) at hz
      rw [CategoryTheory.comp_apply] at hz
      exact hz
    have hc : Function.Injective
        (ConcreteCategory.hom
          ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2))) := by
      change Function.Injective (ConcreteCategory.hom
        ((skyscraperPresheafStalkOfSpecializes realOrigin (ZMod 2)
          specializes_rfl).hom))
      exact ((type_isIso_iff_bijective _).mp (by infer_instance)).1
    have hsurj :
        Function.Surjective
          (ConcreteCategory.hom
              ((stalkSkyscraperSheafAdjunction realOrigin).counit.app (ZMod 2)) ∘
            ConcreteCategory.hom
              ((TopCat.Sheaf.forget (Type 0) realLine ⋙
                TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) := by
      rw [← hfun]
      exact (constantSheafStalkEquiv (X := realLine) (ZMod 2) realOrigin).symm.surjective
    have hfg : Function.Surjective
        (ConcreteCategory.hom
          ((TopCat.Sheaf.forget (Type 0) realLine ⋙
            TopCat.Presheaf.stalkFunctor (Type 0) realOrigin).map g)) :=
      hsurj.of_comp_left hc
    dsimp [g, realConstantToOriginSkyscraper, realOriginSkyscraper,
      skyscraperSheafFunctor] at hfg ⊢
    exact hfg
  · have hspec : ¬ realOrigin ⤳ x := by
      intro h
      exact hx ((specializes_iff_eq (x := realOrigin) (y := x)).mp h).symm
    let e := skyscraperPresheafStalkOfNotSpecializes realOrigin (ZMod 2) hspec
    have he : Function.Injective (ConcreteCategory.hom e.hom) :=
      ((type_isIso_iff_bijective _).mp (by infer_instance)).1
    intro z
    refine ⟨(constantSheafStalkEquiv (X := realLine) (ZMod 2) x) (0 : ZMod 2), ?_⟩
    apply he
    exact Subsingleton.elim _ _

/-- The canonical stalk-surjective map is an epimorphism of sheaves. -/
theorem realConstantToOriginSkyscraper_is_epi :
    Epi realConstantToOriginSkyscraper := by
  exact (sheaf_epi_iff_stalk_surjective realConstantToOriginSkyscraper).2
    realConstantToOriginSkyscraper_stalk_surjective

/-- The set-valued kernel is the equalizer used in the example. -/
theorem realKernel_is_equalizer :
    realKernelSheaf =
      limit (parallelPair realConstantToOriginSkyscraper
        realConstantToOriginSkyscraperZero) := rfl

/-- The additive kernel is an ideal sheaf in the constant `ZMod 2` ring
sheaf. -/
theorem realIdealSheaf_is_ideal :
    IsIdealSheafIn realRingConstantZModTwo realIdealSheaf := by
  classical
  unfold IsIdealSheafIn
  let J := Opens.grothendieckTopology realLine
  letI : PreservesLimits commRingToAddCommGrp := by
    change PreservesLimits
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)
    infer_instance
  letI : J.HasSheafCompose commRingToAddCommGrp :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize (J := J)
      (F := commRingToAddCommGrp)
  letI : J.WEqualsLocallyBijective CommRingCat := inferInstance
  letI : J.WEqualsLocallyBijective AddCommGrpCat := inferInstance
  letI : J.PreservesSheafification commRingToAddCommGrp :=
    { le := by
        intro P Q f hf
        rw [J.W_iff_isLocallyBijective (A := CommRingCat) f] at hf
        change J.W (Functor.whiskerRight f commRingToAddCommGrp)
        rw [J.W_iff_isLocallyBijective (A := AddCommGrpCat)]
        constructor
        · refine { equalizerSieve_mem := ?_ }
          intro X x y h
          change (ConcreteCategory.hom (f.app X)) x =
            (ConcreteCategory.hom (f.app X)) y at h
          exact hf.1.equalizerSieve_mem x y h
        · refine { imageSieve_mem := ?_ }
          intro X x
          have heq :
              Presheaf.imageSieve (Functor.whiskerRight f commRingToAddCommGrp) x =
                Presheaf.imageSieve f x := by
            ext Y g
            change (∃ t, (ConcreteCategory.hom (f.app (op Y))) t =
                (ConcreteCategory.hom (Q.map g.op)) x) ↔
              ∃ t, (ConcreteCategory.hom (f.app (op Y))) t =
                (ConcreteCategory.hom (Q.map g.op)) x
            rfl
          rw [heq]
          exact hf.2.imageSieve_mem x }
  let e :=
    ((CategoryTheory.constantCommuteCompose J commRingToAddCommGrp).app
      (CommRingCat.of (ZMod 2))).symm
  let hmono : Mono realIdealSheafInclusion := by
    constructor
    intro Z f g h
    apply limit.hom_ext
    intro j
    rcases j with (_ | _)
    · exact h
    · rw [← limit.w
        (parallelPair realAbelianConstantToOriginSkyscraper
          realAbelianConstantToOriginSkyscraperZero)
        WalkingParallelPairHom.left]
      have hh := congrArg (fun k => k ≫
          (parallelPair realAbelianConstantToOriginSkyscraper
            realAbelianConstantToOriginSkyscraperZero).map
            WalkingParallelPairHom.left) h
      rw [Category.assoc, Category.assoc] at hh
      exact hh
  let hpmono : Mono realIdealSheafInclusion.hom :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology realLine) AddCommGrpCat
      realIdealSheafInclusion).1 hmono
  let hemono : Mono e.hom.hom :=
    (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono J AddCommGrpCat e.hom).1
      (by infer_instance)
  let hcomp : Mono (realIdealSheafInclusion.hom ≫ e.hom.hom) :=
    mono_comp' hpmono hemono
  refine ⟨realIdealSheafInclusion.hom ≫ e.hom.hom, hcomp, ?_⟩
  intro U
  have hUall := (CategoryTheory.NatTrans.mono_iff_mono_app
    (realIdealSheafInclusion.hom ≫ e.hom.hom)).1 hcomp
  have hU := hUall (op U)
  let RSk :=
    (skyscraperSheafFunctor realOrigin (C := CommRingCat)).obj
      (CommRingCat.of (ZMod 2))
  let rTopIso : RSk.presheaf.obj (op (⊤ : Opens realLine)) ≅
      CommRingCat.of (ZMod 2) := by
    dsimp [RSk]
    change (if realOrigin ∈ (⊤ : Opens realLine) then CommRingCat.of (ZMod 2)
      else terminal CommRingCat) ≅ CommRingCat.of (ZMod 2)
    exact eqToIso (if_pos (by simp))
  let q : realRingConstantZModTwo ⟶ RSk := by
    classical
    exact
      ((CategoryTheory.constantSheafAdj J CommRingCat
        (isTerminalTop : IsTerminal (⊤ : Opens realLine))).homEquiv
        (CommRingCat.of (ZMod 2)) RSk).symm
        (rTopIso.inv ≫
          (CategoryTheory.sheafSectionsNatIsoEvaluation J CommRingCat
            (X := (⊤ : Opens realLine))).inv.app RSk)
  let zIso : AddCommGrpCat.of (ZMod 2) ≅
      commRingToAddCommGrp.obj (CommRingCat.of (ZMod 2)) := by
    refine ⟨AddCommGrpCat.ofHom (AddMonoidHom.id (ZMod 2)),
      AddCommGrpCat.ofHom (AddMonoidHom.id (ZMod 2)), ?_, ?_⟩
    · ext
      rfl
    · ext
      rfl
  let aIsoP : realAbelianOriginSkyscraper.presheaf ≅
      ((CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk).obj := by
    refine NatIso.ofComponents (fun V => ?_) (fun {V W} f => ?_)
    ·
      dsimp [CategoryTheory.ObjectProperty.lift, CategoryTheory.sheafCompose,
        RSk, realAbelianOriginSkyscraper, skyscraperSheaf, skyscraperPresheaf]
      by_cases h : realOrigin ∈ V.unop
      · have hA : (if realOrigin ∈ V.unop then AddCommGrpCat.of (ZMod 2)
            else ⊤_ AddCommGrpCat) = AddCommGrpCat.of (ZMod 2) := if_pos h
        have hR : (((skyscraperSheafFunctor realOrigin (C := CommRingCat)).obj
            (CommRingCat.of (ZMod 2))).obj.obj V) = CommRingCat.of (ZMod 2) := by
          dsimp [skyscraperSheafFunctor, skyscraperSheaf, skyscraperPresheaf]
          simp [h]
        exact eqToIso hA ≪≫ zIso ≪≫
          (eqToIso (congrArg commRingToAddCommGrp.obj hR)).symm
      · simpa [h, RSk, realAbelianOriginSkyscraper,
          CategoryTheory.sheafCompose, skyscraperSheafFunctor,
          skyscraperSheaf, skyscraperPresheaf] using
          (terminalIsTerminal : IsTerminal (⊤_ AddCommGrpCat)).uniqueUpToIso
            (IsTerminal.isTerminalObj commRingToAddCommGrp
              (⊤_ CommRingCat)
              (terminalIsTerminal : IsTerminal (⊤_ CommRingCat)))
    · by_cases hV : realOrigin ∈ V.unop
      · by_cases hW : realOrigin ∈ W.unop
        · simp [hV, hW, RSk, realAbelianOriginSkyscraper,
            CategoryTheory.sheafCompose, skyscraperSheafFunctor,
            skyscraperSheaf, skyscraperPresheaf, skyscraperPresheaf_map,
            eqToHom_trans, eqToIso.hom, eqToHom_map]
          split_ifs with hV'
          · ext x
            simp [ConcreteCategory.comp_apply, type_eqToHom_concrete_apply,
              eqToIso, eqToHom_trans]
          · exact (hV' hV).elim
        · simp [hV, hW, RSk, realAbelianOriginSkyscraper,
            CategoryTheory.sheafCompose, skyscraperSheafFunctor,
            skyscraperSheaf, skyscraperPresheaf, skyscraperPresheaf_map,
            eqToHom_trans, eqToIso.hom, eqToHom_map, zIso]
          have hTW : IsTerminal
              (((CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk).obj.obj W) := by
            dsimp [CategoryTheory.sheafCompose, RSk, skyscraperSheafFunctor,
              skyscraperSheaf, skyscraperPresheaf]
            rw [if_neg hW]
            exact IsTerminal.isTerminalObj commRingToAddCommGrp
              (⊤_ CommRingCat)
              (terminalIsTerminal : IsTerminal (⊤_ CommRingCat))
          exact hTW.hom_ext _ _
      · by_cases hW : realOrigin ∈ W.unop
        · exact (hV (leOfHom f.unop hW)).elim
        · simp [hV, hW, RSk, realAbelianOriginSkyscraper,
            CategoryTheory.sheafCompose, skyscraperSheafFunctor,
            skyscraperSheaf, skyscraperPresheaf, skyscraperPresheaf_map,
            eqToHom_trans, eqToIso.hom, eqToHom_map, zIso]
          have hTW : IsTerminal
              (((CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk).obj.obj W) := by
            dsimp [CategoryTheory.sheafCompose, RSk, skyscraperSheafFunctor,
              skyscraperSheaf, skyscraperPresheaf]
            rw [if_neg hW]
            exact IsTerminal.isTerminalObj commRingToAddCommGrp
              (⊤_ CommRingCat)
              (terminalIsTerminal : IsTerminal (⊤_ CommRingCat))
          exact hTW.hom_ext _ _
  let aIso : realAbelianOriginSkyscraper ≅
      (CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk :=
    (CategoryTheory.fullyFaithfulSheafToPresheaf J AddCommGrpCat).preimageIso aIsoP
  let qAdd : realAbelianConstantZModTwo ⟶ realAbelianOriginSkyscraper :=
    e.hom ≫
      (CategoryTheory.sheafCompose J commRingToAddCommGrp).map q ≫
      aIso.inv
  have hqAdd : qAdd = realAbelianConstantToOriginSkyscraper := by
    let adjA := CategoryTheory.constantSheafAdj J AddCommGrpCat
      (isTerminalTop : IsTerminal (⊤ : Opens realLine))
    let adjR := CategoryTheory.constantSheafAdj J CommRingCat
      (isTerminalTop : IsTerminal (⊤ : Opens realLine))
    let tR : CommRingCat.of (ZMod 2) ⟶ RSk.presheaf.obj
        (op (⊤ : Opens realLine)) :=
      rTopIso.inv ≫
        (CategoryTheory.sheafSectionsNatIsoEvaluation J CommRingCat
          (X := (⊤ : Opens realLine))).inv.app RSk
    let c := CategoryTheory.constantCommuteCompose J commRingToAddCommGrp
    have hqdecomp : q =
        (CategoryTheory.constantSheaf J CommRingCat).map tR ≫
          adjR.counit.app RSk := by
      change ((adjR.homEquiv (CommRingCat.of (ZMod 2)) RSk).symm tR) = _
      exact adjR.homEquiv_counit (CommRingCat.of (ZMod 2)) RSk tR
    have hc_naturality := c.hom.naturality tR
    have hc_naturality' :
        (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              ((CategoryTheory.constantSheaf J CommRingCat).map tR) ≫
            c.hom.app (RSk.presheaf.obj (op (⊤ : Opens realLine))) =
          c.hom.app (CommRingCat.of (ZMod 2)) ≫
            ((commRingToAddCommGrp ⋙ CategoryTheory.constantSheaf J AddCommGrpCat).map
              tR) := by
      simpa only [Functor.comp_map] using hc_naturality
    have hc_naturality'' :
        (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              ((CategoryTheory.constantSheaf J CommRingCat).map tR) ≫
            (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).hom =
          (c.app (CommRingCat.of (ZMod 2))).hom ≫
            ((commRingToAddCommGrp ⋙ CategoryTheory.constantSheaf J AddCommGrpCat).map
              tR) := by
      exact hc_naturality'
    have htransport :
        (c.app (CommRingCat.of (ZMod 2))).inv ≫
            (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              ((CategoryTheory.constantSheaf J CommRingCat).map tR) =
          ((commRingToAddCommGrp ⋙ CategoryTheory.constantSheaf J AddCommGrpCat).map
              tR) ≫
            (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).inv := by
      apply (cancel_mono
        (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).hom).1
      simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
        Category.comp_id] using
        congrArg (fun k =>
          (c.app (CommRingCat.of (ZMod 2))).inv ≫ k) hc_naturality''
    have hcounit :
        (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).inv ≫
            (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              (adjR.counit.app RSk) =
          adjA.counit.app
            ((CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk) := by
      rw [← CategoryTheory.constantSheafAdj_counit_w
        (J := J) (U := commRingToAddCommGrp) (F := RSk)
        (hT := (isTerminalTop : IsTerminal (⊤ : Opens realLine)))]
      change (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).inv ≫
          (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).hom ≫ _ = _
      exact (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).inv_hom_id_assoc _
    let tA : AddCommGrpCat.of (ZMod 2) ⟶
        ((CategoryTheory.sheafSections J AddCommGrpCat).obj
          (op (⊤ : Opens realLine))).obj realAbelianOriginSkyscraper :=
      realOriginSkyscraperTopSectionsIso.inv ≫
        (CategoryTheory.sheafSectionsNatIsoEvaluation J AddCommGrpCat
          (X := (⊤ : Opens realLine))).inv.app
          realAbelianOriginSkyscraper
    have htopObj : realAbelianOriginSkyscraper.presheaf.obj
        (op (⊤ : Opens realLine)) = AddCommGrpCat.of (ZMod 2) := by
      dsimp [realAbelianOriginSkyscraper, skyscraperSheaf,
        skyscraperPresheaf]
      simp
    have htopIso : realOriginSkyscraperTopSectionsIso = eqToIso htopObj := by
      apply Iso.ext
      cases htopObj
      simp [realOriginSkyscraperTopSectionsIso, eqToIso]
    have hsection :
        ((commRingToAddCommGrp.map tR) ≫
        ((CategoryTheory.sheafSections J AddCommGrpCat).obj
            (op (⊤ : Opens realLine))).map aIso.inv) = tA := by
      dsimp [aIso]
      change (commRingToAddCommGrp.map tR) ≫
          (aIsoP.app (op (⊤ : Opens realLine))).inv = tA
      dsimp [tA]
      rw [htopIso]
      dsimp [aIsoP, tA, tR, NatIso.ofComponents]
      ext x
      have h : realOrigin ∈ (⊤ : Opens realLine) := by simp
      have h' : realOrigin ∈ (op (⊤ : Opens realLine)).unop := h
      simp only [dif_pos h']
      simp [rTopIso, zIso, realOriginSkyscraperTopSectionsIso,
        realAbelianOriginSkyscraper, CategoryTheory.sheafCompose,
        CategoryTheory.comp_apply, ConcreteCategory.comp_apply,
        type_eqToHom_concrete_apply,
        eqToIso, eqToIso_refl, eqToHom_refl, eqToHom_trans,
        eqToHom_trans_assoc, eqToHom_map, Category.id_comp, Category.comp_id]
    rw [show realAbelianConstantToOriginSkyscraper =
      (adjA.homEquiv (AddCommGrpCat.of (ZMod 2))
        realAbelianOriginSkyscraper).symm tA by
      rfl]
    rw [show qAdd =
      (adjA.homEquiv (AddCommGrpCat.of (ZMod 2))
        realAbelianOriginSkyscraper).symm
        ((commRingToAddCommGrp.map tR) ≫
          ((CategoryTheory.sheafSections J AddCommGrpCat).obj
            (op (⊤ : Opens realLine))).map aIso.inv) by
      change (c.app (CommRingCat.of (ZMod 2))).inv ≫
          (CategoryTheory.sheafCompose J commRingToAddCommGrp).map q ≫ aIso.inv = _
      calc
        _ = (c.app (CommRingCat.of (ZMod 2))).inv ≫
            (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              ((CategoryTheory.constantSheaf J CommRingCat).map tR ≫
                adjR.counit.app RSk) ≫ aIso.inv := by
          rw [show q =
            (CategoryTheory.constantSheaf J CommRingCat).map tR ≫
              adjR.counit.app RSk from hqdecomp]
        _ = (c.app (CommRingCat.of (ZMod 2))).inv ≫
            ((CategoryTheory.sheafCompose J commRingToAddCommGrp).map
                ((CategoryTheory.constantSheaf J CommRingCat).map tR) ≫
              (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
                (adjR.counit.app RSk)) ≫ aIso.inv := by
          rw [Functor.map_comp]
        _ = ((commRingToAddCommGrp ⋙ CategoryTheory.constantSheaf J AddCommGrpCat).map tR ≫
              (c.app (RSk.presheaf.obj (op (⊤ : Opens realLine)))).inv) ≫
            (CategoryTheory.sheafCompose J commRingToAddCommGrp).map
              (adjR.counit.app RSk) ≫ aIso.inv := by
          simp only [Category.assoc]
          rw [htransport]
        _ = (commRingToAddCommGrp ⋙ CategoryTheory.constantSheaf J AddCommGrpCat).map tR ≫
            adjA.counit.app ((CategoryTheory.sheafCompose J commRingToAddCommGrp).obj RSk) ≫
              aIso.inv := by
          rw [Category.assoc, hcounit]
        _ = (adjA.homEquiv (AddCommGrpCat.of (ZMod 2))
            realAbelianOriginSkyscraper).symm
              ((commRingToAddCommGrp.map tR) ≫
                ((CategoryTheory.sheafSections J AddCommGrpCat).obj
                  (op (⊤ : Opens realLine))).map aIso.inv) := by
          rw [CategoryTheory.Adjunction.homEquiv_counit]
          simp]
    exact congrArg
      ((adjA.homEquiv (AddCommGrpCat.of (ZMod 2))
        realAbelianOriginSkyscraper).symm) hsection

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

/-- The constant singleton functor on sheaves over the empty space is exact. -/
theorem emptySheafExactFunctor_is_exact :
    @IsExact (Sh.{v, v} emptyTopologicalSpace) _ (Type v) _
      inferInstance emptySheafHasFiniteColimits emptySheafExactFunctor := by
  sorry

/-- The empty-space constant functor is not a stalk functor because the space
has no points. -/
theorem emptySheafExactFunctor_not_a_stalk_functor :
    ¬ IsStalkFunctor emptySheafExactFunctor := by
  sorry

/-- A concrete witness for the exact functor exercise. -/
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
