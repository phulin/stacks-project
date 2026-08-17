import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.CategoryTheory.Limits.Fubini
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Categories, Chapter 14: Limits and colimits

The chapter's diagram, cone, and cocone language is formalized with the
canonical Mathlib APIs.  In particular, `Cone`/`IsLimit` and
`Cocone`/`IsColimit` provide the definitions and universal properties, while
the declarations below record the chapter-facing interfaces and constructions.
-/

namespace Formalization.Books.Categories.Unit14

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite

universe u v u' v' w w'

noncomputable section

section BasicLanguage

variable (I : Type u) [Category.{v} I]
variable (C : Type u') [Category.{v'} C]

/-- A chapter diagram is the canonical Mathlib notion of a functor. -/
abbrev Diagram := I ⥤ C

/- In this notation `M.obj i` is the source's `M_i`, and `M.map φ` is its
`M(φ)`.  The index category is the domain `I` of the functor. -/

variable {I C}
variable (M : I ⥤ C)

/-- The limit universal property, in the family-of-projections form used in the text. -/
theorem limit_universal_property {c : Cone M} (hc : IsLimit c) (s : Cone M) :
    ∃! q : s.pt ⟶ c.pt, ∀ i, q ≫ c.π.app i = s.π.app i :=
  hc.existsUnique s

/-- The dual colimit universal property, in the family-of-inclusions form. -/
theorem colimit_universal_property {c : Cocone M} (hc : IsColimit c) (s : Cocone M) :
    ∃! q : c.pt ⟶ s.pt, ∀ i, c.ι.app i ≫ q = s.ι.app i :=
  hc.existsUnique s

/-- Two limit cones are uniquely isomorphic in a way compatible with their legs. -/
theorem limit_cone_unique_up_to_unique_iso {c d : Cone M} (hc : IsLimit c) (hd : IsLimit d) :
    ∃! e : c.pt ≅ d.pt, ∀ i, e.hom ≫ d.π.app i = c.π.app i := by
  let e := hc.conePointUniqueUpToIso hd
  refine ⟨e, ?_, ?_⟩
  · intro i
    exact hc.conePointUniqueUpToIso_hom_comp hd i
  · intro e' he'
    apply Iso.ext
    apply hd.hom_ext
    intro i
    exact (he' i).trans (hc.conePointUniqueUpToIso_hom_comp hd i).symm

/-- Two cocones are uniquely isomorphic in a way compatible with their legs. -/
theorem colimit_cocone_unique_up_to_unique_iso {c d : Cocone M} (hc : IsColimit c)
    (hd : IsColimit d) :
    ∃! e : c.pt ≅ d.pt, ∀ i, c.ι.app i ≫ e.hom = d.ι.app i := by
  let e := hc.coconePointUniqueUpToIso hd
  refine ⟨e, ?_, ?_⟩
  · intro i
    exact IsColimit.comp_coconePointUniqueUpToIso_hom hc hd i
  · intro e' he'
    apply Iso.ext
    apply hc.hom_ext
    intro i
    exact (he' i).trans (IsColimit.comp_coconePointUniqueUpToIso_hom hc hd i).symm

/-- Cones form the category in which a limit cone is a terminal object. -/
def limit_cone_is_terminal_equiv {c : Cone M} : IsLimit c ≃ IsTerminal c :=
  Cone.isLimitEquivIsTerminal c

theorem has_limit_iff_terminal_cones : HasLimit M ↔ HasTerminal (Cone M) :=
  hasLimit_iff_hasTerminal_cone M

/-- Cocones form the category in which a colimit cocone is an initial object. -/
def colimit_cocone_is_initial_equiv {c : Cocone M} : IsColimit c ≃ IsInitial c :=
  Cocone.isColimitEquivIsInitial c

theorem has_colimit_iff_initial_cocones : HasColimit M ↔ HasInitial (Cocone M) :=
  hasColimit_iff_hasInitial_cocone M

/-- The hom-set form of the limit universal property. -/
def limit_hom_cone_iso (W : C) [HasLimit M] :
    ULift.{u} (W ⟶ limit M) ≅ M.cones.obj (op W) :=
  limit.homIso M W

/-- The hom-set form of the colimit universal property. -/
def colimit_hom_cocone_iso (W : C) [HasColimit M] :
    ULift.{u} (colimit M ⟶ W) ≅ M.cocones.obj W :=
  colimit.homIso M W

/- These cone and cocone categories are the canonical set-valued limits in
the displayed hom-set formulas; their determination of the object is the
Yoneda content of the source remark. -/

end BasicLanguage

section EmptyDiagramsAndSets

variable (C : Type u') [Category.{v'} C]

/- The source excludes diagrams indexed by a proper class.  The explicit
`Type` index and `Small` hypothesis in the set-valued statements below are
the universe-sensitive Lean form of that restriction. -/

def empty_diagram_limit_is_terminal {J : Type u} [Category.{v} J] [IsEmpty J]
    {M : J ⥤ C} {c : Cone M} (hc : IsLimit c) : IsTerminal c.pt :=
  (isLimitEquivIsTerminalOfIsEmpty C c) hc

def empty_diagram_colimit_is_initial {J : Type u} [Category.{v} J] [IsEmpty J]
    {M : J ⥤ C} {c : Cocone M} (hc : IsColimit c) : IsInitial c.pt :=
  (isColimitEquivIsInitialOfIsEmpty C c) hc

theorem types_have_small_limits {J : Type w} [Category.{v} J] [Small.{u} J] :
    HasLimitsOfShape J (Type u) := by
  infer_instance

theorem types_have_small_colimits {J : Type w} [Category.{v} J] [Small.{u} J] :
    HasColimitsOfShape J (Type u) := by
  infer_instance

end EmptyDiagramsAndSets

section ProductsAndExamples

variable {C : Type u} [Category.{v} C]

/-- Products are limits of discrete diagrams, via Mathlib's canonical product API. -/
def product_is_limit (M : I → C) [HasProduct M] :
    IsLimit (Fan.mk (∏ᶜ M) (Pi.π M)) :=
  productIsProduct M

/-- Coproducts are colimits of discrete diagrams, via Mathlib's canonical API. -/
def coproduct_is_colimit (M : I → C) [HasCoproduct M] :
    IsColimit (Cofan.mk (∐ M) (Sigma.ι M)) :=
  coproductIsCoproduct M

def binary_product_example {X Y : C} [HasLimit (pair X Y)] :
    IsLimit (limit.cone (pair X Y)) :=
  limit.isLimit _

def pullback_example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] :
    IsLimit (pullback.cone f g) :=
  pullback.isLimit f g

def equalizer_example {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] :
    IsLimit (Fork.ofι (equalizer.ι f g) (equalizer.condition f g)) :=
  equalizerIsEqualizer f g

def binary_coproduct_example {X Y : C} [HasColimit (pair X Y)] :
    IsColimit (colimit.cocone (pair X Y)) :=
  colimit.isColimit _

def pushout_example {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g] :
    IsColimit (pushout.cocone f g) :=
  pushout.isColimit f g

def coequalizer_example {X Y : C} (f g : X ⟶ Y) [HasCoequalizer f g] :
    IsColimit (Cofork.ofπ (coequalizer.π f g) (coequalizer.condition f g)) :=
  coequalizerIsCoequalizer f g

/- The empty product and coproduct assertions are the `PEmpty` specializations
of `product_is_limit`, `coproduct_is_colimit`, and the two empty-diagram
equivalences above. -/

end ProductsAndExamples

section Functoriality

variable {I J C : Type*}
variable [Category I] [Category J] [Category C]

/-- The map on chosen colimits induced by a functor and a natural transformation. -/
def inducedColimitMap {M : I ⥤ C} {N : J ⥤ C} [HasColimit M] [HasColimit N]
    (H : I ⥤ J) (t : M ⟶ H ⋙ N) : colimit M ⟶ colimit N :=
  colimit.desc M
    { pt := colimit N
      ι := t ≫ ((colimit.cocone N).whisker H).ι }

theorem inducedColimitMap_ι {M : I ⥤ C} {N : J ⥤ C} [HasColimit M] [HasColimit N]
    (H : I ⥤ J) (t : M ⟶ H ⋙ N) (i : I) :
    colimit.ι M i ≫ inducedColimitMap H t = t.app i ≫ colimit.ι N (H.obj i) := by
  simp [inducedColimitMap]

theorem existsUnique_inducedColimitMap {M : I ⥤ C} {N : J ⥤ C} [HasColimit M] [HasColimit N]
    (H : I ⥤ J) (t : M ⟶ H ⋙ N) :
    ∃! θ : colimit M ⟶ colimit N,
      ∀ i, colimit.ι M i ≫ θ = t.app i ≫ colimit.ι N (H.obj i) := by
  sorry

/-- The map on chosen limits induced by a functor and a natural transformation. -/
def inducedLimitMap {M : I ⥤ C} {N : J ⥤ C} [HasLimit M] [HasLimit N]
    (H : I ⥤ J) (t : H ⋙ N ⟶ M) : limit N ⟶ limit M :=
  limit.lift M
    { pt := limit N
      π := ((limit.cone N).whisker H).π ≫ t }

theorem inducedLimitMap_π {M : I ⥤ C} {N : J ⥤ C} [HasLimit M] [HasLimit N]
    (H : I ⥤ J) (t : H ⋙ N ⟶ M) (i : I) :
    inducedLimitMap H t ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  simp [inducedLimitMap]

theorem existsUnique_inducedLimitMap {M : I ⥤ C} {N : J ⥤ C} [HasLimit M] [HasLimit N]
    (H : I ⥤ J) (t : H ⋙ N ⟶ M) :
    ∃! θ : limit N ⟶ limit M,
      ∀ i, θ ≫ limit.π M i = limit.π N (H.obj i) ≫ t.app i := by
  sorry

end Functoriality

section Fubini

variable {I J C : Type*}
variable [Category I] [Category J] [Category C]

/-- The pointwise inner colimits appearing in the chapter's iterated-colimit statement. -/
def pointwiseColimit (M : I ⥤ J ⥤ C) (h : ∀ i, HasColimit (M.obj i)) : I ⥤ C where
  obj i := colimit (M.obj i)
  map f := colimMap (M.map f)
  map_id i := by
    apply colimit.hom_ext
    intro j
    simp
  map_comp f g := by
    apply colimit.hom_ext
    intro j
    simp [Category.assoc]

/-- The pointwise inner limits appearing in the dual iterated-limit statement. -/
def pointwiseLimit (M : I ⥤ J ⥤ C) (h : ∀ i, HasLimit (M.obj i)) : I ⥤ C where
  obj i := limit (M.obj i)
  map f := limMap (M.map f)
  map_id i := by
    apply limit.hom_ext
    intro j
    simp
  map_comp f g := by
    apply limit.hom_ext
    intro j
    simp [Category.assoc]

theorem has_colimit_uncurry_iff_pointwiseColimit (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasColimit (M.obj i)) :
    HasColimit (Functor.uncurry.obj M) ↔ HasColimit (pointwiseColimit M h) := by
  sorry

theorem has_limit_uncurry_iff_pointwiseLimit (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasLimit (M.obj i)) :
    HasLimit (Functor.uncurry.obj M) ↔ HasLimit (pointwiseLimit M h) := by
  sorry

theorem iterated_colimits_are_colimit (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasColimit (M.obj i)) [HasColimit (Functor.uncurry.obj M)]
    [HasColimit (pointwiseColimit M h)] :
    Nonempty (colimit (pointwiseColimit M h) ≅ colimit (Functor.uncurry.obj M)) := by
  sorry

theorem iterated_limits_are_limit (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasLimit (M.obj i)) [HasLimit (Functor.uncurry.obj M)]
    [HasLimit (pointwiseLimit M h)] :
    Nonempty (limit (pointwiseLimit M h) ≅ limit (Functor.uncurry.obj M)) := by
  sorry

theorem iterated_colimits_can_be_swapped (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasColimit (M.obj i))
    (h' : ∀ j, HasColimit (M.flip.obj j))
    [HasColimit (Functor.uncurry.obj M)] [HasColimit (pointwiseColimit M h)]
    [HasColimit (pointwiseColimit M.flip h')] :
    Nonempty
      (colimit (pointwiseColimit M h) ≅
        colimit (pointwiseColimit M.flip h')) := by
  sorry

theorem iterated_limits_can_be_swapped (M : I ⥤ J ⥤ C)
    (h : ∀ i, HasLimit (M.obj i))
    (h' : ∀ j, HasLimit (M.flip.obj j))
    [HasLimit (Functor.uncurry.obj M)] [HasLimit (pointwiseLimit M h)]
    [HasLimit (pointwiseLimit M.flip h')] :
    Nonempty
      (limit (pointwiseLimit M h) ≅
        limit (pointwiseLimit M.flip h')) := by
  sorry

end Fubini

section ProductsAndEqualizersConstruction

variable {I : Type u} {C : Type u'} [SmallCategory I] [Category.{v'} C]

/-- The index type of all arrows of a category, used in the standard construction. -/
abbrev ArrowIndex := Σ p : I × I, p.1 ⟶ p.2

noncomputable def limitProductMap (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)] :
    (∏ᶜ fun i : I => M.obj i) ⟶ ∏ᶜ fun a : ArrowIndex => M.obj a.1.2 :=
  Pi.lift fun a => Pi.π (fun i : I => M.obj i) a.1.1 ≫ M.map a.2

noncomputable def limitProductMap' (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)] :
    (∏ᶜ fun i : I => M.obj i) ⟶ ∏ᶜ fun a : ArrowIndex => M.obj a.1.2 :=
  Pi.lift fun a => Pi.π (fun i : I => M.obj i) a.1.2

theorem limitProductMap_comp_projection (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)] (a : ArrowIndex) :
    limitProductMap M ≫ Pi.π (fun a : ArrowIndex => M.obj a.1.2) a =
      Pi.π (fun i : I => M.obj i) a.1.1 ≫ M.map a.2 := by
  simp [limitProductMap]

theorem limitProductMap'_comp_projection (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)] (a : ArrowIndex) :
    limitProductMap' M ≫ Pi.π (fun a : ArrowIndex => M.obj a.1.2) a =
      Pi.π (fun i : I => M.obj i) a.1.2 := by
  simp [limitProductMap']

noncomputable def limitConeFromProductsAndEqualizer (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)]
    [HasEqualizer (limitProductMap M) (limitProductMap' M)] :
    LimitCone M :=
  let s := limitProductMap M
  let t := limitProductMap' M
  let hs : ∀ a : ArrowIndex,
      s ≫ Pi.π (fun a : ArrowIndex => M.obj a.1.2) a =
        Pi.π (fun i : I => M.obj i) a.1.1 ≫ M.map a.2 :=
    fun a => limitProductMap_comp_projection M a
  let ht : ∀ a : ArrowIndex,
      t ≫ Pi.π (fun a : ArrowIndex => M.obj a.1.2) a =
        Pi.π (fun i : I => M.obj i) a.1.2 :=
    fun a => limitProductMap'_comp_projection M a
  let i := Fork.ofι (equalizer.ι s t) (equalizer.condition s t)
  { cone := HasLimitOfHasProductsOfHasEqualizers.buildLimit s t hs ht i
    isLimit := HasLimitOfHasProductsOfHasEqualizers.buildIsLimit s t hs ht
      (productIsProduct (fun i : I => M.obj i))
      (productIsProduct (fun a : ArrowIndex => M.obj a.1.2))
      (equalizerIsEqualizer s t) }

theorem has_limit_of_products_and_equalizer (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)]
    [HasEqualizer (limitProductMap M) (limitProductMap' M)] :
    HasLimit M := by
  exact ⟨⟨limitConeFromProductsAndEqualizer (I := I) (C := C) M⟩⟩

def equalizer_is_limit_of_products_and_equalizer (M : I ⥤ C)
    [HasProduct (fun i : I => M.obj i)]
    [HasProduct (fun a : ArrowIndex => M.obj a.1.2)]
    [HasEqualizer (limitProductMap M) (limitProductMap' M)] :
    IsLimit (limitConeFromProductsAndEqualizer M).cone :=
  (limitConeFromProductsAndEqualizer M).isLimit

noncomputable def colimitCoproductMap (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)] :
    (∐ fun a : ArrowIndex => M.obj a.1.1) ⟶ ∐ fun i : I => M.obj i :=
  Sigma.desc fun a => M.map a.2 ≫ Sigma.ι (fun i : I => M.obj i) a.1.2

noncomputable def colimitCoproductMap' (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)] :
    (∐ fun a : ArrowIndex => M.obj a.1.1) ⟶ ∐ fun i : I => M.obj i :=
  Sigma.desc fun a => Sigma.ι (fun i : I => M.obj i) a.1.1

theorem colimitCoproductMap_inclusion (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)] (a : ArrowIndex) :
    Sigma.ι (fun a : ArrowIndex => M.obj a.1.1) a ≫ colimitCoproductMap M =
      M.map a.2 ≫ Sigma.ι (fun i : I => M.obj i) a.1.2 := by
  simp [colimitCoproductMap]

theorem colimitCoproductMap'_inclusion (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)] (a : ArrowIndex) :
    Sigma.ι (fun a : ArrowIndex => M.obj a.1.1) a ≫ colimitCoproductMap' M =
      Sigma.ι (fun i : I => M.obj i) a.1.1 := by
  simp [colimitCoproductMap']

noncomputable def colimitCoconeFromCoproductsAndCoequalizer (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)]
    [HasCoequalizer (colimitCoproductMap M) (colimitCoproductMap' M)] :
    ColimitCocone M :=
  let s := colimitCoproductMap M
  let t := colimitCoproductMap' M
  let hs : ∀ a : ArrowIndex,
      Sigma.ι (fun a : ArrowIndex => M.obj a.1.1) a ≫ s =
        M.map a.2 ≫ Sigma.ι (fun i : I => M.obj i) a.1.2 :=
    fun a => colimitCoproductMap_inclusion M a
  let ht : ∀ a : ArrowIndex,
      Sigma.ι (fun a : ArrowIndex => M.obj a.1.1) a ≫ t =
        Sigma.ι (fun i : I => M.obj i) a.1.1 :=
    fun a => colimitCoproductMap'_inclusion M a
  let i := Cofork.ofπ (coequalizer.π s t) (coequalizer.condition s t)
  { cocone := HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit s t hs ht i
    isColimit := HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit s t hs ht
      (coproductIsCoproduct (fun a : ArrowIndex => M.obj a.1.1))
      (coproductIsCoproduct (fun i : I => M.obj i))
      (coequalizerIsCoequalizer s t) }

theorem has_colimit_of_coproducts_and_coequalizer (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)]
    [HasCoequalizer (colimitCoproductMap M) (colimitCoproductMap' M)] :
    HasColimit M := by
  exact ⟨⟨colimitCoconeFromCoproductsAndCoequalizer (I := I) (C := C) M⟩⟩

def coequalizer_is_colimit_of_coproducts_and_coequalizer (M : I ⥤ C)
    [HasCoproduct (fun i : I => M.obj i)]
    [HasCoproduct (fun a : ArrowIndex => M.obj a.1.1)]
    [HasCoequalizer (colimitCoproductMap M) (colimitCoproductMap' M)] :
    IsColimit (colimitCoconeFromCoproductsAndCoequalizer M).cocone :=
  (colimitCoconeFromCoproductsAndCoequalizer M).isColimit

theorem has_limits_of_products_and_equalizers
    [HasProducts.{v} C] [HasEqualizers C] : HasLimitsOfSize.{v, v} C :=
  has_limits_of_hasEqualizers_and_products

theorem has_colimits_of_coproducts_and_coequalizers
    [HasCoproducts.{v} C] [HasCoequalizers C] : HasColimitsOfSize.{v, v} C :=
  has_colimits_of_hasCoequalizers_and_coproducts

end ProductsAndEqualizersConstruction

end
end Formalization.Books.Categories.Unit14
