import Formalization.Books.Sheaves.Unit11.Stalks
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 21: Continuous maps and sheaves

The source section is `books/sheaves.tex:1984-2399`.  Pushforward and
pullback are Mathlib's canonical functors on presheaves and sheaves.  In
particular, the pullback presheaf is the pointwise left Kan extension along
the functor on open sets, so its value is presented by the colimit over the
canonical costructured-arrow category of open neighbourhoods.  The `f`-map
interface below uses the corresponding canonical sheaf morphism and adds the
source's section-family presentation as a bridge.
-/

namespace Formalization.Books.Sheaves.Unit21

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit11

universe v

noncomputable section

/-! ## Pushforward of presheaves and sheaves -/

/-!
The following aliases expose Mathlib's canonical constructions under the
source's names.  Their object and morphism fields are exactly the inverse
image and restriction maps displayed in the source.
-/

/-- Pushforward of set-valued presheaves along a continuous map. -/
abbrev pushforwardPresheaf {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Presheaf.{v, v} X ⥤ Presheaf.{v, v} Y :=
  TopCat.Presheaf.pushforward (Type v) f

/-- Pushforward of set-valued sheaves along a continuous map. -/
abbrev pushforwardSheaf {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Sh.{v, v} X ⥤ Sh.{v, v} Y :=
  TopCat.Sheaf.pushforward (Type v) f

/-- The value of a pushforward presheaf is the value on the inverse image. -/
@[simp]
theorem pushforwardPresheaf_obj_obj {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Presheaf.{v, v} X) (V : Opens Y) :
    ((pushforwardPresheaf f).obj F).obj (op V) =
      F.obj (op ((Opens.map f).obj V)) := rfl

/-- The restriction maps of a pushforward are the original restriction maps. -/
@[simp]
theorem pushforwardPresheaf_map {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Presheaf.{v, v} X) {V W : Opens Y} (h : V ≤ W) :
    ((pushforwardPresheaf f).obj F).map (homOfLE h).op =
      F.map (((Opens.map f).op).map (homOfLE h).op) := rfl

/-- Pushforward on presheaf morphisms is computed componentwise. -/
@[simp]
theorem pushforwardPresheaf_map_app {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F G : Presheaf.{v, v} X} (φ : F ⟶ G) (V : Opens Y) :
    ((pushforwardPresheaf f).map φ).app (op V) =
      φ.app (((Opens.map f).op).obj (op V)) := rfl

/-- A sheaf remains a sheaf after pushforward. -/
theorem pushforwardPresheaf_isSheaf {X Y : TopCat.{v}} (f : X ⟶ Y)
    {F : Presheaf.{v, v} X} (hF : SetSheaf F) :
    SetSheaf ((pushforwardPresheaf f).obj F) := by
  exact TopCat.Sheaf.pushforward_sheaf_of_sheaf f hF

/-- The underlying presheaf of sheaf pushforward is presheaf pushforward. -/
@[simp]
theorem pushforwardSheaf_obj_presheaf {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Sh.{v, v} X) :
    ((pushforwardSheaf f).obj F).presheaf =
      (pushforwardPresheaf f).obj F.presheaf := rfl

/-- Pushforward commutes with composition, on presheaves. -/
theorem pushforwardPresheaf_comp_obj {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (F : Presheaf.{v, v} X) :
    (pushforwardPresheaf (f ≫ g)).obj F =
      (pushforwardPresheaf g).obj ((pushforwardPresheaf f).obj F) := by
  exact TopCat.Presheaf.Pushforward.comp_eq f g F

/-- Pushforward commutes with composition, on sheaves. -/
noncomputable def pushforwardSheafCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pushforwardSheaf f ⋙ pushforwardSheaf g ≅ pushforwardSheaf (f ≫ g) :=
  Iso.refl _

/-! ## Pullback presheaves -/

/-- Pullback of set-valued presheaves, as the canonical left Kan extension. -/
abbrev pullbackPresheaf {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Presheaf.{v, v} Y ⥤ Presheaf.{v, v} X :=
  TopCat.Presheaf.pullback (Type v) f

/-- The canonical index category for the pullback value on an open `U`. -/
abbrev pullbackIndex {X Y : TopCat.{v}} (f : X ⟶ Y) (U : Opens X) :=
  CostructuredArrow (Opens.map f).op (op U)

/-- The diagram of sections indexed by open neighbourhoods of `f(U)`. -/
abbrev pullbackDiagram {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Presheaf.{v, v} Y) (U : Opens X) :
    pullbackIndex f U ⥤ Type v :=
  CostructuredArrow.proj (Opens.map f).op (op U) ⋙ G

/-- The pullback value is the colimit over open neighbourhoods of `f(U)`. -/
noncomputable def pullbackPresheaf_obj_colimitIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Presheaf.{v, v} Y) (U : Opens X) :
    ((pullbackPresheaf f).obj G).obj (op U) ≅ colimit (pullbackDiagram f G U) :=
  Functor.leftKanExtensionObjIsoColimit (Opens.map f).op G (op U)

/-- The neighbourhood index category is directed (in the categorical sense). -/
theorem pullbackIndex_isFiltered {X Y : TopCat.{v}} (f : X ⟶ Y) (U : Opens X) :
    IsFiltered (pullbackIndex f U) := by
  infer_instance

/-- The pullback and pushforward presheaf functors are adjoint. -/
noncomputable abbrev pullbackPresheafPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullbackPresheaf f ⊣ pushforwardPresheaf f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction (Type v) f

/-- The unit `G → f_* f_p G` of the presheaf adjunction. -/
noncomputable abbrev pullbackPresheafUnit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Presheaf.{v, v} Y) :
    G ⟶ (pushforwardPresheaf f).obj ((pullbackPresheaf f).obj G) :=
  (pullbackPresheafPushforwardAdjunction f).unit.app G

/-- The counit `f_p f_* F → F` of the presheaf adjunction. -/
noncomputable abbrev pullbackPresheafCounit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Presheaf.{v, v} X) :
    (pullbackPresheaf f).obj ((pushforwardPresheaf f).obj F) ⟶ F :=
  (pullbackPresheafPushforwardAdjunction f).counit.app F

/-- The hom-set bijection expressing the presheaf pullback adjunction. -/
noncomputable abbrev pullbackPresheafHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Presheaf.{v, v} Y) (F : Presheaf.{v, v} X) :
    ((pullbackPresheaf f).obj G ⟶ F) ≃
      (G ⟶ (pushforwardPresheaf f).obj F) :=
  (pullbackPresheafPushforwardAdjunction f).homEquiv G F

/-- The stalk identification for the pullback presheaf. -/
noncomputable def pullbackPresheafStalkIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Presheaf.{v, v} Y) (x : X) :
    G.stalk (f x) ≅ ((pullbackPresheaf f).obj G).stalk x :=
  TopCat.Presheaf.stalkPullbackIso (Type v) f G x

/-- The source's bijection `(f_p G)_x ≃ G_{f(x)}`, oriented as an equivalence. -/
noncomputable def pullbackPresheafStalkEquiv {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Presheaf.{v, v} Y) (x : X) :
    ((pullbackPresheaf f).obj G).stalk x ≃ G.stalk (f x) :=
  (pullbackPresheafStalkIso f G x).toEquiv.symm

/-- Pullback presheaves commute with composition, canonically. -/
noncomputable def pullbackPresheafCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackPresheaf (f ≫ g) ≅ pullbackPresheaf g ⋙ pullbackPresheaf f := by
  exact Adjunction.leftAdjointUniq
    (pullbackPresheafPushforwardAdjunction (f ≫ g))
    ((pullbackPresheafPushforwardAdjunction g).comp
      (pullbackPresheafPushforwardAdjunction f))

/-! ## Pullback sheaves -/

/-- Pullback of set-valued sheaves, using Mathlib's canonical sheaf functor. -/
noncomputable abbrev pullbackSheaf {X Y : TopCat.{v}} (f : X ⟶ Y) :
    Sh.{v, v} Y ⥤ Sh.{v, v} X :=
  TopCat.Sheaf.pullback (Type v) f

/-- The source's sheafification description of pullback. -/
noncomputable def pullbackSheaf_sheafificationIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Sh.{v, v} Y) :
    (pullbackSheaf f).obj G ≅
      (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) (Type v)).obj
        ((pullbackPresheaf f).obj G.presheaf) :=
  (TopCat.Sheaf.pullbackIso (Type v) f).app G

/-- The pullback and pushforward sheaf functors are adjoint. -/
noncomputable abbrev pullbackSheafPushforwardAdjunction
    {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullbackSheaf f ⊣ pushforwardSheaf f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction (Type v) f

/-- The unit `G → f_* f⁻¹ G` of the sheaf adjunction. -/
noncomputable abbrev pullbackSheafUnit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) : G ⟶ (pushforwardSheaf f).obj ((pullbackSheaf f).obj G) :=
  (pullbackSheafPushforwardAdjunction f).unit.app G

/-- The counit `f⁻¹ f_* F → F` of the sheaf adjunction. -/
noncomputable abbrev pullbackSheafCounit {X Y : TopCat.{v}} (f : X ⟶ Y)
    (F : Sh.{v, v} X) :
    (pullbackSheaf f).obj ((pushforwardSheaf f).obj F) ⟶ F :=
  (pullbackSheafPushforwardAdjunction f).counit.app F

/-- The hom-set bijection expressing the sheaf pullback adjunction. -/
noncomputable abbrev pullbackSheafHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) :
    ((pullbackSheaf f).obj G ⟶ F) ≃ (G ⟶ (pushforwardSheaf f).obj F) :=
  (pullbackSheafPushforwardAdjunction f).homEquiv G F

/-- The stalk identification for the pullback sheaf. -/
noncomputable def pullbackSheafStalkIso {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Sh.{v, v} Y) (x : X) :
    G.presheaf.stalk (f x) ≅ ((pullbackSheaf f).obj G).presheaf.stalk x := by
  let e := pullbackSheaf_sheafificationIso f G
  let e' := (CategoryTheory.sheafToPresheaf
    (Opens.grothendieckTopology X) (Type v)).mapIso e
  let P := (pullbackPresheaf f).obj G.presheaf
  let u := (TopCat.Presheaf.stalkFunctor (Type v) x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P)
  letI : IsIso u := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (X := X) (p₀ := x) (C := Type v) P
  exact (pullbackPresheafStalkIso f G.presheaf x).trans <|
    (asIso u).trans <| (TopCat.Presheaf.stalkFunctor (Type v) x).mapIso e'.symm

/-- The source's bijection `(f⁻¹ G)_x ≃ G_{f(x)}`, oriented as an equivalence. -/
noncomputable def pullbackSheafStalkEquiv {X Y : TopCat.{v}}
    (f : X ⟶ Y) (G : Sh.{v, v} Y) (x : X) :
    ((pullbackSheaf f).obj G).presheaf.stalk x ≃ G.presheaf.stalk (f x) :=
  (pullbackSheafStalkIso f G x).toEquiv.symm

/-- Pullback sheaves commute with composition, canonically. -/
noncomputable def pullbackSheafCompIso {X Y Z : TopCat.{v}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullbackSheaf (f ≫ g) ≅ pullbackSheaf g ⋙ pullbackSheaf f := by
  exact Adjunction.leftAdjointUniq
    (pullbackSheafPushforwardAdjunction (f ≫ g))
    ((pullbackSheafPushforwardAdjunction g).comp
      (pullbackSheafPushforwardAdjunction f))

/-! ## `f`-maps -/

/-- An `f`-map is the canonical map of sheaves `G → f_* F`. -/
abbrev FMap {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) : Type _ :=
  G ⟶ (pushforwardSheaf f).obj F

/-- The component of an `f`-map on sections over `V`. -/
abbrev fMapAt {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : Sh.{v, v} Y} {F : Sh.{v, v} X} (ξ : FMap f G F) (V : Opens Y) :
    Sections G.presheaf V → Sections F.presheaf ((Opens.map f).obj V) :=
  ξ.hom.app (op V)

/-- The source's set of compatible two-open section families. -/
structure FMapFamily {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) where
  /-- The map attached to `U ⊆ f⁻¹(V)`. -/
  app : ∀ (U : Opens X) (V : Opens Y), U ≤ (Opens.map f).obj V →
    Sections G.presheaf V → Sections F.presheaf U
  /-- Compatibility with restriction in both open variables. -/
  naturality : ∀ {U U' : Opens X} {V V' : Opens Y}
    (hUU' : U' ≤ U) (hVV' : V' ≤ V)
    (hU : U ≤ (Opens.map f).obj V) (hU' : U' ≤ (Opens.map f).obj V')
    (s : Sections G.presheaf V),
    restriction (F := F.presheaf) hUU' (app U V hU s) =
      app U' V' hU' (restriction (F := G.presheaf) hVV' s)

/-- The section-family presentation associated to an `f`-map. -/
def fMapFamilyOfFMap {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : Sh.{v, v} Y} {F : Sh.{v, v} X} (ξ : FMap f G F) :
    FMapFamily f G F where
  app U V h s := restriction (F := F.presheaf) h (fMapAt ξ V s)
  naturality := by
    sorry

/-- An `f`-map obtained from the source's compatible two-open family. -/
def fMapOfFamily {X Y : TopCat.{v}} {f : X ⟶ Y}
    {G : Sh.{v, v} Y} {F : Sh.{v, v} X} (ξ : FMapFamily f G F) : FMap f G F :=
  (CategoryTheory.Sheaf.homEquiv).symm
    { app := fun V => TypeCat.ofHom (fun s =>
        ξ.app ((Opens.map f).obj V.unop) V.unop le_rfl s)
      naturality := by
        sorry }

/-- The first and third entries in the source's four-way correspondence. -/
noncomputable abbrev fMapSheafHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) :
    (G ⟶ (pushforwardSheaf f).obj F) ≃ FMap f G F :=
  Equiv.refl _

/-- The second entry in the source's four-way correspondence. -/
noncomputable abbrev fMapPullbackHomEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) :
    ((pullbackSheaf f).obj G ⟶ F) ≃ FMap f G F :=
  pullbackSheafHomEquiv f G F

/-- The fourth entry in the source's four-way correspondence. -/
noncomputable def fMapFamilyEquiv {X Y : TopCat.{v}} (f : X ⟶ Y)
    (G : Sh.{v, v} Y) (F : Sh.{v, v} X) :
    FMap f G F ≃ FMapFamily f G F where
  toFun := fMapFamilyOfFMap
  invFun := fMapOfFamily
  left_inv := by
    sorry
  right_inv := by
    sorry

/-! ## Composition and stalks of `f`-maps -/

/-- Composition of an `f`-map and a `g`-map. -/
noncomputable def fMapComp {X Y Z : TopCat.{v}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : Sh.{v, v} X} {G : Sh.{v, v} Y} {H : Sh.{v, v} Z}
    (φ : FMap f G F) (ψ : FMap g H G) : FMap (f ≫ g) H F :=
  ψ ≫ (pushforwardSheaf g).map φ ≫
    (pushforwardSheafCompIso f g).hom.app F

/-- The map on stalks induced by an `f`-map. -/
noncomputable def fMapStalkMap {X Y : TopCat.{v}}
    {f : X ⟶ Y} {G : Sh.{v, v} Y} {F : Sh.{v, v} X}
    (ξ : FMap f G F) (x : X) :
    Stalk G.presheaf (f x) → Stalk F.presheaf x :=
  fun s =>
    ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward
      (Type v) f F.presheaf x)
      (ConcreteCategory.hom ((TopCat.Presheaf.stalkFunctor
        (Type v) (f x)).map ξ.hom) s)

/-- The representative formula for the map on stalks. -/
theorem fMapStalkMap_germ {X Y : TopCat.{v}}
    {f : X ⟶ Y} {G : Sh.{v, v} Y} {F : Sh.{v, v} X}
    (ξ : FMap f G F) (x : X) (V : Opens Y) (hx : f x ∈ V)
    (s : Sections G.presheaf V) :
    fMapStalkMap ξ x (germApply (F := G.presheaf) V (f x) hx s) =
      germApply (F := F.presheaf) ((Opens.map f).obj V) x hx
        (fMapAt ξ V s) := by
  sorry

/-- The representative formula uniquely characterizes the stalk map. -/
theorem fMapStalkMap_unique {X Y : TopCat.{v}}
    {f : X ⟶ Y} {G : Sh.{v, v} Y} {F : Sh.{v, v} X}
    (ξ : FMap f G F) (x : X)
    (φ : Stalk G.presheaf (f x) → Stalk F.presheaf x)
    (hφ : ∀ (V : Opens Y) (hx : f x ∈ V) (s : Sections G.presheaf V),
      φ (germApply (F := G.presheaf) V (f x) hx s) =
        germApply (F := F.presheaf) ((Opens.map f).obj V) x hx
          (fMapAt ξ V s)) :
    φ = fMapStalkMap ξ x := by
  sorry

/-- Stalk maps carry composition of `f`-maps to composition of functions. -/
theorem fMapComp_stalkMap {X Y Z : TopCat.{v}}
    {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : Sh.{v, v} X} {G : Sh.{v, v} Y} {H : Sh.{v, v} Z}
    (φ : FMap f G F) (ψ : FMap g H G) (x : X) :
    fMapStalkMap (fMapComp φ ψ) x =
      fMapStalkMap φ x ∘ fMapStalkMap ψ (f x) := by
  sorry

end

end Formalization.Books.Sheaves.Unit21
