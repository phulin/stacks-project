import Formalization.Books.Sheaves.Unit21.ContinuousMaps
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit12.StalksOfAbelianPresheaves
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 22, Section 1: Continuous maps and abelian sheaves

The set-valued constructions from Chapter 21 are reused with the canonical
`AddCommGrpCat`-valued presheaf and sheaf categories.  In particular, the
pullback is Mathlib's left Kan extension and the inverse image of a sheaf is
the corresponding sheaf pullback.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit21

universe v

noncomputable section

/-! ## Abelian presheaf and sheaf functors -/

/-- Pushforward of abelian presheaves along a continuous map. -/
abbrev abelianPresheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AbelianPresheaf X ⥤ AbelianPresheaf Y :=
  TopCat.Presheaf.pushforward (AddCommGrpCat.{v}) f

/-- Pushforward of abelian sheaves along a continuous map. -/
abbrev abelianSheafPushforward {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Ab X ⥤ Ab Y :=
  TopCat.Sheaf.pushforward (AddCommGrpCat.{v}) f

/-- Pullback of abelian presheaves, as a left Kan extension. -/
abbrev abelianPresheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    AbelianPresheaf Y ⥤ AbelianPresheaf X :=
  TopCat.Presheaf.pullback (AddCommGrpCat.{v}) f

/-- Pullback of abelian sheaves. -/
abbrev abelianSheafPullback {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Ab Y ⥤ Ab X :=
  TopCat.Sheaf.pullback (AddCommGrpCat.{v}) f

@[simp]
theorem abelianPresheafPushforward_obj_obj {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : AbelianPresheaf X) (V : Opens Y) :
    ((abelianPresheafPushforward f).obj F).obj (op V) =
      F.obj (op ((Opens.map f).obj V)) := rfl

@[simp]
theorem abelianPresheafPushforward_map {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : AbelianPresheaf X) {V W : Opens Y} (h : V ≤ W) :
    ((abelianPresheafPushforward f).obj F).map (homOfLE h).op =
      F.map (((Opens.map f).op).map (homOfLE h).op) := rfl

noncomputable def abelianPresheafPullback_obj_colimitIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : AbelianPresheaf Y) (U : Opens X) :
    ((abelianPresheafPullback f).obj G).obj (op U) ≅
      colimit
        (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G) :=
  Functor.leftKanExtensionObjIsoColimit (Opens.map f).op G (op U)

theorem abelianSheafPushforward_obj_presheaf {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Ab X) :
    ((abelianSheafPushforward f).obj F).presheaf =
      (abelianPresheafPushforward f).obj F.presheaf := rfl

/-- Pushforward preserves the sheaf condition in abelian groups. -/
theorem abelianPresheafPushforward_isSheaf {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F : AbelianPresheaf X} (hF : TopCat.Presheaf.IsSheaf F) :
    TopCat.Presheaf.IsSheaf ((abelianPresheafPushforward f).obj F) := by
  exact TopCat.Sheaf.pushforward_sheaf_of_sheaf f hF

/-! ## Presheaf adjunction and stalks -/

/-- The pullback/pushforward adjunction for abelian presheaves. -/
noncomputable abbrev abelianPresheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    abelianPresheafPullback f ⊣ abelianPresheafPushforward f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) f

/-- The unit of the abelian presheaf pullback adjunction. -/
noncomputable abbrev abelianPresheafUnit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AbelianPresheaf Y) :
    G ⟶ (abelianPresheafPushforward f).obj ((abelianPresheafPullback f).obj G) :=
  (abelianPresheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit of the abelian presheaf pullback adjunction. -/
noncomputable abbrev abelianPresheafCounit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : AbelianPresheaf X) :
    (abelianPresheafPullback f).obj ((abelianPresheafPushforward f).obj F) ⟶ F :=
  (abelianPresheafPullbackPushforwardAdjunction f).counit.app F

/-- The Hom-set bijection for the abelian presheaf adjunction. -/
noncomputable abbrev abelianPresheafHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : AbelianPresheaf Y) (F : AbelianPresheaf X) :
    ((abelianPresheafPullback f).obj G ⟶ F) ≃
      (G ⟶ (abelianPresheafPushforward f).obj F) :=
  (abelianPresheafPullbackPushforwardAdjunction f).homEquiv G F

/-- The canonical additive stalk isomorphism for presheaf pullback. -/
noncomputable def abelianPresheafPullbackStalkIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : AbelianPresheaf Y) (x : X) :
    G.stalk (f x) ≅ ((abelianPresheafPullback f).obj G).stalk x :=
  TopCat.Presheaf.stalkPullbackIso (AddCommGrpCat.{v}) f G x

/-- Pullback presheaves commute with composition. -/
noncomputable def abelianPresheafPullbackCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    abelianPresheafPullback (f ≫ g) ≅
      abelianPresheafPullback g ⋙ abelianPresheafPullback f := by
  exact Adjunction.leftAdjointUniq
    (abelianPresheafPullbackPushforwardAdjunction (f ≫ g))
    ((abelianPresheafPullbackPushforwardAdjunction g).comp
      (abelianPresheafPullbackPushforwardAdjunction f))

/-- Pushforward presheaves commute with composition. -/
noncomputable def abelianPresheafPushforwardCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    abelianPresheafPushforward f ⋙ abelianPresheafPushforward g ≅
      abelianPresheafPushforward (f ≫ g) :=
  Iso.refl _

/-- Pushforward abelian sheaves commutes with composition. -/
noncomputable def abelianSheafPushforwardCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    abelianSheafPushforward f ⋙ abelianSheafPushforward g ≅
      abelianSheafPushforward (f ≫ g) :=
  Iso.refl _

/-! ## Abelian sheaf pullback -/

/-- The sheaf pullback is sheafification of the presheaf pullback. -/
noncomputable def abelianSheafPullback_sheafificationIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Ab Y) :
    (abelianSheafPullback f).obj G ≅
      (CategoryTheory.presheafToSheaf
        (Opens.grothendieckTopology X) AddCommGrpCat).obj
        ((abelianPresheafPullback f).obj G.presheaf) :=
  (TopCat.Sheaf.pullbackIso (AddCommGrpCat.{v}) f).app G

/-- The pullback/pushforward adjunction for abelian sheaves. -/
noncomputable abbrev abelianSheafPullbackPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    abelianSheafPullback f ⊣ abelianSheafPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (AddCommGrpCat.{v}) f

/-- The unit of the abelian sheaf pullback adjunction. -/
noncomputable abbrev abelianSheafUnit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Ab Y) :
    G ⟶ (abelianSheafPushforward f).obj ((abelianSheafPullback f).obj G) :=
  (abelianSheafPullbackPushforwardAdjunction f).unit.app G

/-- The counit of the abelian sheaf pullback adjunction. -/
noncomputable abbrev abelianSheafCounit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Ab X) :
    (abelianSheafPullback f).obj ((abelianSheafPushforward f).obj F) ⟶ F :=
  (abelianSheafPullbackPushforwardAdjunction f).counit.app F

/-- The Hom-set bijection for the abelian sheaf adjunction. -/
noncomputable abbrev abelianSheafHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Ab Y) (F : Ab X) :
    ((abelianSheafPullback f).obj G ⟶ F) ≃
      (G ⟶ (abelianSheafPushforward f).obj F) :=
  (abelianSheafPullbackPushforwardAdjunction f).homEquiv G F

/-- The canonical additive stalk isomorphism for sheaf pullback. -/
noncomputable def abelianSheafPullbackStalkIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Ab Y) (x : X) :
    G.presheaf.stalk (f x) ≅
      ((abelianSheafPullback f).obj G).presheaf.stalk x := by
  let e := abelianSheafPullback_sheafificationIso f G
  let e' := (CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology X) AddCommGrpCat).mapIso e
  let P := (abelianPresheafPullback f).obj G.presheaf
  let u := (TopCat.Presheaf.stalkFunctor
    (AddCommGrpCat.{v}) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
  letI : IsIso u := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := X) (p₀ := x) (C := AddCommGrpCat.{v}) P
  exact (TopCat.Presheaf.stalkPullbackIso
      (AddCommGrpCat.{v}) f G.presheaf x).trans <|
    (asIso u).trans <|
      (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).mapIso e'.symm

/-! ## Abelian `f`-maps -/

/-- An abelian `f`-map is a morphism of abelian sheaves to the pushforward. -/
abbrev AbelianFMap {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Ab Y) (F : Ab X) : Type _ :=
  G ⟶ (abelianSheafPushforward f).obj F

/-- The set of abelian `f`-maps is the Hom-set of the pushforward target. -/
noncomputable abbrev abelianFMapHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Ab Y) (F : Ab X) :
    AbelianFMap f G F ≃ (G ⟶ (abelianSheafPushforward f).obj F) :=
  Equiv.refl _

/-- The abelian `f`-map/pullback Hom correspondence. -/
noncomputable abbrev abelianFMapPullbackHomEquiv {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Ab Y) (F : Ab X) :
    ((abelianSheafPullback f).obj G ⟶ F) ≃ AbelianFMap f G F :=
  abelianSheafHomEquiv f G F

/-- Composition of an abelian `f`-map and an abelian `g`-map. -/
noncomputable def abelianFMapComp {X Y Z : TopCat.{v}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : Ab X} {G : Ab Y} {H : Ab Z}
    (φ : AbelianFMap f G F) (ψ : AbelianFMap g H G) :
    AbelianFMap (f ≫ g) H F :=
  ψ ≫ (abelianSheafPushforward g).map φ ≫
    (abelianSheafPushforwardCompIso f g).hom.app F

/-- The additive map on stalks induced by an abelian `f`-map. -/
noncomputable def abelianFMapStalkMap {X Y : TopCat.{v}}
    {f : X ⟶ Y} {G : Ab Y} {F : Ab X}
    (ξ : AbelianFMap f G F) (x : X) :
    G.presheaf.stalk (f x) ⟶ F.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) (f x)).map ξ.hom ≫
    F.presheaf.stalkPushforward (AddCommGrpCat.{v}) f x

/-! ## Source-facing assertions -/

theorem abelianFMapComp_stalkMap {X Y Z : TopCat.{v}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : Ab X} {G : Ab Y} {H : Ab Z}
    (φ : AbelianFMap f G F) (ψ : AbelianFMap g H G) (x : X) :
    abelianFMapStalkMap (abelianFMapComp φ ψ) x =
      abelianFMapStalkMap ψ (f x) ≫ abelianFMapStalkMap φ x := by
  sorry

end

end Formalization.Books.Sheaves.Unit22
