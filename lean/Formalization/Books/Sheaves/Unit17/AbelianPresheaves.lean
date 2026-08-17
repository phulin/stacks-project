import Formalization.Books.Sheaves.Unit12.StalksOfAbelianPresheaves
import Formalization.Books.Sheaves.Unit17.Sheafification
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheaves on Spaces, Chapter 17, Section 2: Sheafification of abelian presheaves

The source span is `books/sheaves.tex:1664-1774`.  The categorical
`AddCommGrpCat`-valued sheafification and its unit are Mathlib's canonical
ones.  The stalkwise set presentation from the preceding section is retained
through explicit four-corner maps and a `Type`-valued pullback statement.
-/

namespace Formalization.Books.Sheaves.Unit17

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit11

universe v

noncomputable section

/-! ## The canonical abelian sheafification -/

/-- The `AddCommGrpCat`-valued sheafification of an abelian presheaf. -/
noncomputable def abelianSheafification {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) : TopCat.Sheaf AddCommGrpCat.{v} X :=
  (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
    AddCommGrpCat).obj F

/-- The underlying presheaf of the canonical abelian sheafification. -/
abbrev abelianSheafificationPresheaf {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) : TopCat.Presheaf AddCommGrpCat.{v} X :=
  (abelianSheafification F).presheaf

/-- The canonical additive map from an abelian presheaf to its sheafification. -/
noncomputable def abelianSheafificationUnit {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :
    F ⟶ abelianSheafificationPresheaf F :=
  CategoryTheory.toSheafify (Opens.grothendieckTopology X) F

/-- The underlying set sheaf of the categorical construction is isomorphic to
the stalk-local-germ construction. -/
theorem abelianSheafification_underlying_iso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :
    Nonempty
      (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (CategoryTheory.forget AddCommGrpCat) (abelianSheafification F).presheaf ≅
        (sheafification (underlyingPresheaf F)).presheaf) := by
  let J := Opens.grothendieckTopology X
  let P := underlyingPresheaf F
  let G : TopCat.Sheaf (Type v) X :=
    ⟨Formalization.Books.Sheaves.Unit05.underlyingPresheaf
        (forget AddCommGrpCat) (abelianSheafification F).presheaf,
      (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (forget AddCommGrpCat) (abelianSheafification F).presheaf).mp
        (abelianSheafification F).property⟩
  let H : TopCat.Sheaf (Type v) X :=
    (CategoryTheory.presheafToSheaf J (Type v)).obj P
  let p := CategoryTheory.sheafifyLift J (sheafificationUnit P)
    (sheafification_isSheaf P)
  let q := sheafificationLift P H (CategoryTheory.toSheafify J P)
  have hp : CategoryTheory.toSheafify J P ≫ p = sheafificationUnit P := by
    exact CategoryTheory.toSheafify_sheafifyLift _ _ _
  have hq : sheafificationUnit P ≫ q = CategoryTheory.toSheafify J P := by
    exact sheafificationUnit_comp_lift P H (CategoryTheory.toSheafify J P)
  have hqp : q ≫ p = 𝟙 _ := by
    have h₁ : q ≫ p =
        sheafificationLift P (sheafification P) (sheafificationUnit P) := by
      apply sheafificationLift_unique P (sheafification P) (sheafificationUnit P)
      rw [← Category.assoc, hq, hp]
    have h₂ : (𝟙 _) =
        sheafificationLift P (sheafification P) (sheafificationUnit P) :=
      sheafificationLift_unique P (sheafification P) (sheafificationUnit P) (𝟙 _)
        (by simp)
    exact h₁.trans h₂.symm
  have hpq : p ≫ q = 𝟙 _ := by
    apply CategoryTheory.sheafify_hom_ext J (p ≫ q) (𝟙 _) H.property
    rw [← Category.assoc, hp, hq]
    simp
  let eLocal : H.presheaf ≅ (sheafification P).presheaf :=
    { hom := p, inv := q, hom_inv_id := hpq, inv_hom_id := hqp }
  let e := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J
    (CategoryTheory.forget AddCommGrpCat)
  let eF := e.app F
  let eK0 := (CategoryTheory.sheafToPresheaf J (Type v)).mapIso eF
  let iG := CategoryTheory.isoSheafify J G.property
  let iG' : G.presheaf ≅
      (CategoryTheory.sheafToPresheaf J (Type v)).obj
        ((CategoryTheory.presheafToSheaf J (Type v)).obj G.presheaf) := by
    exact iG
  have eGH : G.presheaf ≅ H.presheaf := by
    simpa [P, G, H,
      Formalization.Books.Sheaves.Unit04.underlyingPresheaf,
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf,
      abelianSheafification, CategoryTheory.Sheaf.composeAndSheafify] using
      (iG'.trans eK0)
  let eFinal : G.presheaf ≅ (sheafification P).presheaf :=
    eGH ≪≫ eLocal
  exact ⟨eFinal⟩

/-! ## The four maps in the fibre-product diagram -/

abbrev abelianFibreProductSetPresheaf {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) : TopCat.Presheaf (Type v) X :=
  underlyingPresheaf F

abbrev abelianFibreProductStalkProduct {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) : TopCat.Presheaf (Type v) X :=
  stalkProductPresheaf (underlyingPresheaf F)

/-- The top horizontal map `F#(U) → Π(F)(U)`. -/
abbrev abelianFibreProduct_top {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    (sheafificationPresheaf (underlyingPresheaf F)).obj (op U) ⟶
      (abelianFibreProductStalkProduct F).obj (op U) :=
  (sheafificationProductMap (underlyingPresheaf F)).app (op U)

/-- The left vertical map `F#(U) → ∏ x∈U Fₓ`, using the subtype carrier. -/
def abelianFibreProduct_left {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    (sheafificationPresheaf (underlyingPresheaf F)).obj (op U) ⟶
      (∀ x : U, (underlyingPresheaf F).stalk x) :=
  TypeCat.ofHom (fun s => s.1)

/-- The right vertical map `Π(F)(U) → ∏ x∈U Π(F)ₓ`. -/
abbrev abelianFibreProduct_right {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    (abelianFibreProductStalkProduct F).obj (op U) ⟶
      (∀ x : U, (abelianFibreProductStalkProduct F).stalk x) :=
  (presheafToStalkProduct (abelianFibreProductStalkProduct F)).app (op U)

/-- The bottom horizontal map, componentwise induced by `Fₓ → Π(F)ₓ`. -/
def abelianFibreProduct_bottom {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    (∀ x : U, (underlyingPresheaf F).stalk x) ⟶
      (∀ x : U, (abelianFibreProductStalkProduct F).stalk x) :=
  TypeCat.ofHom (fun s x =>
    (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (presheafToStalkProduct (underlyingPresheaf F)) (s x))

/-! ## The general fibre-product diagram -/

/-- The stalkwise product presheaf in the source's fibre-product lemma. -/
abbrev fibreProductStalkProduct {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) : TopCat.Presheaf (Type v) X :=
  stalkProductPresheaf F

/-- The top horizontal map in the source's general fibre-product diagram. -/
abbrev fibreProduct_top {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) ⟶
      (fibreProductStalkProduct F).obj (op U) :=
  (sheafificationProductMap F).app (op U)

/-- The left vertical map in the source's general fibre-product diagram. -/
def fibreProduct_left {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) ⟶
      (∀ x : U, F.stalk x) :=
  TypeCat.ofHom (fun s => s.1)

/-- The right vertical map in the source's general fibre-product diagram. -/
abbrev fibreProduct_right {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (fibreProductStalkProduct F).obj (op U) ⟶
      (∀ x : U, (fibreProductStalkProduct F).stalk x) :=
  (presheafToStalkProduct (fibreProductStalkProduct F)).app (op U)

/-- The bottom horizontal map in the source's general fibre-product diagram. -/
def fibreProduct_bottom {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    (∀ x : U, F.stalk x) ⟶
      (∀ x : U, (fibreProductStalkProduct F).stalk x) :=
  TypeCat.ofHom (fun s x =>
    (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (presheafToStalkProduct F) (s x))

/-- The source's general four-corner diagram is a pullback in `Type`. -/
theorem sheafification_fibreProduct {X : TopCat.{v}}
    (F : TopCat.Presheaf (Type v) X) (U : Opens X) :
    IsPullback (fibreProduct_top F U) (fibreProduct_left F U)
      (fibreProduct_right F U) (fibreProduct_bottom F U) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro s
    funext x
    obtain ⟨V, hxV, i, σ, hs⟩ :=
      (sheafificationCondition_iff F s.1).mp s.2 x
    have hsx : s.1 x = F.germ V x.1 hxV σ := by
      have hi : i ⟨x.1, hxV⟩ = x := by
        apply Subtype.ext
        rfl
      have h := hs ⟨x.1, hxV⟩
      simpa [hi] using h
    have hrestr :
        (fibreProductStalkProduct F).map i.op s.1 =
          (presheafToStalkProduct F).app (op V) σ := by
      funext y
      change s.1 (i y) = F.germ V y.1 y.2 σ
      exact hs y
    change
      (fibreProductStalkProduct F).germ U x.1 x.2 s.1 =
        (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
          (presheafToStalkProduct F) (s.1 x)
    have hleft :
        (fibreProductStalkProduct F).germ U x.1 x.2 s.1 =
          (fibreProductStalkProduct F).germ V x.1 hxV
            ((presheafToStalkProduct F).app (op V) σ) := by
      calc
        _ = (fibreProductStalkProduct F).germ V x.1 hxV
            ((fibreProductStalkProduct F).map i.op s.1) := by
          simpa using
            ((fibreProductStalkProduct F).germ_res_apply i x.1 hxV s.1).symm
        _ = _ := congrArg _ hrestr
    have hright :
        (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (presheafToStalkProduct F) (s.1 x) =
          (fibreProductStalkProduct F).germ V x.1 hxV
            ((presheafToStalkProduct F).app (op V) σ) := by
      rw [hsx, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact hleft.trans hright.symm
  · intro T φ φ' htop hleft
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    have h := congrArg (fun f => (ConcreteCategory.hom f) t) htop
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  · intro T a b hab
    have hprod (x : X) :
        Function.Injective
          ((TopCat.Presheaf.stalkFunctor (Type v) x).map
            (presheafToStalkProduct F)) := by
      intro r s hrs
      have hinj :
          Function.Injective
            ((TopCat.Presheaf.stalkFunctor (Type v) x).map
              (sheafificationProductMap F)) :=
        TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
          (fun V => by
            intro r s hrs'
            exact Subtype.ext hrs') x
      apply (sheafificationUnit_stalk_bijective F x).1
      apply hinj
      rw [presheafToStalkProduct, CategoryTheory.Functor.map_comp,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hrs
      exact hrs
    have hab_tx (t : T) (x : U) :
        (fibreProductStalkProduct F).germ U x.1 x.2 (a t) =
          (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (presheafToStalkProduct F) (b t x) := by
      have h := congrArg (fun f => (ConcreteCategory.hom f) t) hab
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
      have hx := congrFun h x
      change
        (fibreProductStalkProduct F).germ U x.1 x.2 (a t) =
          (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (presheafToStalkProduct F) (b t x) at hx
      exact hx
    have hb (t : T) : sheafificationCondition F (b t) := by
      apply (sheafificationCondition_iff F (b t)).2
      intro x
      obtain ⟨V, hVU, hxV, σ, hσ⟩ :=
        F.exists_le_germ_eq (b t x) x.2
      have hgm :
          (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
              (presheafToStalkProduct F) (F.germ V x.1 hxV σ) =
            (fibreProductStalkProduct F).germ V x.1 hxV
              ((presheafToStalkProduct F).app (op V) σ) := by
        simpa only [fibreProductStalkProduct] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
            (presheafToStalkProduct F) σ)
      have hxmap :
          (fibreProductStalkProduct F).germ U x.1 x.2 (a t) =
            (fibreProductStalkProduct F).germ V x.1 hxV
              ((presheafToStalkProduct F).app (op V) σ) := by
        exact (hab_tx t x).trans <|
          (congrArg
            (fun z => (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
              (presheafToStalkProduct F) z) hσ.symm).trans hgm
      obtain ⟨W, hxW, iWU, iWV, hW⟩ :=
        (fibreProductStalkProduct F).germ_eq x x.2 hxV (a t)
          ((presheafToStalkProduct F).app (op V) σ) hxmap
      refine ⟨W, hxW, iWU, F.map iWV.op σ, ?_⟩
      intro y
      apply hprod y.1
      have hres :
          (fibreProductStalkProduct F).germ U y.1 (iWU.le y.2) (a t) =
            (fibreProductStalkProduct F).germ W y.1 y.2
              ((fibreProductStalkProduct F).map iWU.op (a t)) := by
        simpa only [fibreProductStalkProduct] using
          ((fibreProductStalkProduct F).germ_res_apply iWU y.1 y.2 (a t)).symm
      have hy1 :
          (TopCat.Presheaf.stalkFunctor (Type v) y.1).map
              (presheafToStalkProduct F) (b t (iWU y)) =
            (fibreProductStalkProduct F).germ U y.1 (iWU.le y.2)
              (a t) := by
        simpa using (hab_tx t (iWU y)).symm
      have hy2 := congrArg
        (fun q => (ConcreteCategory.hom
          ((fibreProductStalkProduct F).germ W y.1 y.2)) q) hW
      have hy3 :
          (fibreProductStalkProduct F).germ W y.1 y.2
              ((fibreProductStalkProduct F).map iWU.op (a t)) =
            (fibreProductStalkProduct F).germ W y.1 y.2
              ((fibreProductStalkProduct F).map iWV.op
                ((presheafToStalkProduct F).app (op V) σ)) := by
        exact hy2
      have hy4 :
          (fibreProductStalkProduct F).germ W y.1 y.2
              ((fibreProductStalkProduct F).map iWV.op
                ((presheafToStalkProduct F).app (op V) σ)) =
            (fibreProductStalkProduct F).germ W y.1 y.2
              ((presheafToStalkProduct F).app (op W) (F.map iWV.op σ)) := by
        congr 1
        have hn := congrArg (fun f => f σ)
          ((presheafToStalkProduct F).naturality iWV.op)
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hn
        exact hn.symm
      have hy5 :
          (fibreProductStalkProduct F).germ W y.1 y.2
              ((presheafToStalkProduct F).app (op W) (F.map iWV.op σ)) =
            (TopCat.Presheaf.stalkFunctor (Type v) y.1).map
              (presheafToStalkProduct F)
              (F.germ W y.1 y.2 (F.map iWV.op σ)) := by
        rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact hy1.trans (hres.trans (hy3.trans (hy4.trans hy5)))
    have hbgerm (t : T) (x : U) :
        (fibreProductStalkProduct F).germ U x.1 x.2 (b t) =
          (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
            (presheafToStalkProduct F) (b t x) := by
      obtain ⟨V, hxV, i, σ, hs⟩ :=
        (sheafificationCondition_iff F (b t)).mp (hb t) x
      have hsx : b t x = F.germ V x.1 hxV σ := by
        have hi : i ⟨x.1, hxV⟩ = x := by
          apply Subtype.ext
          rfl
        have h := hs ⟨x.1, hxV⟩
        simpa [hi] using h
      have hrestr :
          (fibreProductStalkProduct F).map i.op (b t) =
            (presheafToStalkProduct F).app (op V) σ := by
        funext y
        change b t (i y) = F.germ V y.1 y.2 σ
        exact hs y
      have hgm :
          (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
              (presheafToStalkProduct F) (F.germ V x.1 hxV σ) =
            (fibreProductStalkProduct F).germ V x.1 hxV
              ((presheafToStalkProduct F).app (op V) σ) := by
        simpa only [fibreProductStalkProduct] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply V x.1 hxV
            (presheafToStalkProduct F) σ)
      exact
        ((fibreProductStalkProduct F).germ_res_apply i x.1 hxV (b t)).symm.trans <|
          (congrArg (fun z =>
            (fibreProductStalkProduct F).germ V x.1 hxV z) hrestr).trans <|
            hgm.symm.trans <| congrArg
              (fun z => (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
                (presheafToStalkProduct F) z) hsx.symm
    have hsection (t : T) : (a t) = (b t) := by
      apply TopCat.Presheaf.section_ext (stalkProductSheaf F) U
      intro x hx
      exact (hab_tx t ⟨x, hx⟩).trans (hbgerm t ⟨x, hx⟩).symm
    let l : T ⟶ (sheafificationPresheaf F).obj (op U) :=
      TypeCat.ofHom (fun t => ⟨b t, hb t⟩)
    refine ⟨l, ?_, ?_⟩
    · apply ConcreteCategory.hom_ext
      intro t
      change b t = a t
      exact (hsection t).symm
    · apply ConcreteCategory.hom_ext
      intro t
      rfl

/-- The source's four-corner diagram is a pullback in `Type`. -/
theorem abelianSheafification_fibreProduct {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    IsPullback (abelianFibreProduct_top F U) (abelianFibreProduct_left F U)
      (abelianFibreProduct_right F U) (abelianFibreProduct_bottom F U) := by
  exact sheafification_fibreProduct (underlyingPresheaf F) U

/-! ## Additive structure, stalks, and the adjunction -/

/-- A categorical existence package for the additive sheafification and its
underlying stalk-local set presentation. -/
theorem abelianSheafification_structure_exists {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :
    ∃ (A : TopCat.Sheaf AddCommGrpCat.{v} X) (_η : F ⟶ A.presheaf),
      Nonempty
        (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
            (CategoryTheory.forget AddCommGrpCat) A.presheaf ≅
          (sheafification (underlyingPresheaf F)).presheaf) := by
  refine ⟨abelianSheafification F, abelianSheafificationUnit F, ?_⟩
  exact abelianSheafification_underlying_iso F

/-! The fixed-carrier statement from the source is stronger than merely
choosing an isomorphic categorical sheaf. -/

/-- The canonical unit is additive for the unique pointwise abelian-group
structure on the fixed set-valued sheafification. -/
def IsAbelianSheafificationStructure {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X)
    (S : PointwiseAbelianPresheafData
      (sheafificationPresheaf (underlyingPresheaf F))) : Prop :=
  ∀ U : Opens X,
    letI := S.group U
    ∃ η : AbelianSections F U →+
        Sections (sheafificationPresheaf (underlyingPresheaf F)) U,
      ∀ s, η s =
        (sheafificationUnit (underlyingPresheaf F)).app (op U) s

/-- The source's existence and uniqueness assertion for the abelian structure
on `F#` making `F → F#` a morphism of abelian presheaves. -/
theorem existsUnique_abelianSheafificationStructure {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :
    ∃! S : PointwiseAbelianPresheafData
        (sheafificationPresheaf (underlyingPresheaf F)),
      IsAbelianSheafificationStructure F S := by
  let G0 := Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat) (abelianSheafification F).presheaf
  let P := Formalization.Books.Sheaves.Unit05.underlyingPresheaf
    (CategoryTheory.forget AddCommGrpCat) F
  let H := sheafificationPresheaf (underlyingPresheaf F)
  let J := Opens.grothendieckTopology X
  let G : TopCat.Sheaf (Type v) X :=
    ⟨G0, (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
        (forget AddCommGrpCat) (abelianSheafification F).presheaf).mp
        (abelianSheafification F).property⟩
  let H' : TopCat.Sheaf (Type v) X :=
    (CategoryTheory.presheafToSheaf J (Type v)).obj P
  let p := CategoryTheory.sheafifyLift J (sheafificationUnit P)
    (sheafification_isSheaf P)
  let q := sheafificationLift P H' (CategoryTheory.toSheafify J P)
  have hp : CategoryTheory.toSheafify J P ≫ p = sheafificationUnit P := by
    exact CategoryTheory.toSheafify_sheafifyLift _ _ _
  have hq : sheafificationUnit P ≫ q = CategoryTheory.toSheafify J P := by
    exact sheafificationUnit_comp_lift P H' (CategoryTheory.toSheafify J P)
  have hqp : q ≫ p = 𝟙 _ := by
    have h₁ : q ≫ p =
        sheafificationLift P (sheafification P) (sheafificationUnit P) := by
      apply sheafificationLift_unique P (sheafification P) (sheafificationUnit P)
      rw [← Category.assoc, hq, hp]
    have h₂ : (𝟙 _) =
        sheafificationLift P (sheafification P) (sheafificationUnit P) :=
      sheafificationLift_unique P (sheafification P) (sheafificationUnit P) (𝟙 _)
        (by simp)
    exact h₁.trans h₂.symm
  have hpq : p ≫ q = 𝟙 _ := by
    apply CategoryTheory.sheafify_hom_ext J (p ≫ q) (𝟙 _) H'.property
    rw [← Category.assoc, hp, hq]
    simp
  let eLocal : H'.presheaf ≅ (sheafification P).presheaf :=
    { hom := p, inv := q, hom_inv_id := hpq, inv_hom_id := hqp }
  let eComp := CategoryTheory.presheafToSheafCompComposeAndSheafifyIso J
    (CategoryTheory.forget AddCommGrpCat)
  let eF := eComp.app F
  let eK0 := (CategoryTheory.sheafToPresheaf J (Type v)).mapIso eF
  let iG := CategoryTheory.isoSheafify J G.property
  let iG' : G.presheaf ≅
      (CategoryTheory.sheafToPresheaf J (Type v)).obj
        ((CategoryTheory.presheafToSheaf J (Type v)).obj G.presheaf) := by
    exact iG
  let eGH : G.presheaf ≅ H'.presheaf := by
    simpa [P, G, H', G0,
      Formalization.Books.Sheaves.Unit04.underlyingPresheaf,
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf,
      abelianSheafification, CategoryTheory.Sheaf.composeAndSheafify] using
      (iG'.trans eK0)
  let e : G0 ≅ H := by
    simpa [P, H,
      Formalization.Books.Sheaves.Unit04.underlyingPresheaf,
      Formalization.Books.Sheaves.Unit05.underlyingPresheaf] using
      (eGH ≪≫ eLocal)
  have hGH :
      underlyingPresheafMorphism (forget AddCommGrpCat)
          (abelianSheafificationUnit F) ≫ eGH.hom =
        CategoryTheory.toSheafify J P := by
    change underlyingPresheafMorphism (forget AddCommGrpCat)
          (abelianSheafificationUnit F) ≫ iG'.hom ≫ eK0.hom = _
    change (underlyingPresheafMorphism (forget AddCommGrpCat)
          (abelianSheafificationUnit F) ≫
        CategoryTheory.toSheafify J G0) ≫
      (CategoryTheory.sheafToPresheaf J (Type v)).map eF.hom = _
    rw [CategoryTheory.toSheafify_naturality]
    rw [Category.assoc]
    have hα := eComp.inv_hom_id_app F
    change CategoryTheory.toSheafify J
      (F ⋙ (CategoryTheory.forget AddCommGrpCat)) ≫
      (CategoryTheory.sheafToPresheaf J (Type v)).map (eComp.inv.app F) ≫
        (CategoryTheory.sheafToPresheaf J (Type v)).map (eComp.hom.app F) =
      CategoryTheory.toSheafify J (F ⋙ (CategoryTheory.forget AddCommGrpCat))
    rw [← (CategoryTheory.sheafToPresheaf J (Type v)).map_comp,
      hα]
    simp
  have hcomp :
      underlyingPresheafMorphism (forget AddCommGrpCat)
          (abelianSheafificationUnit F) ≫ e.hom =
        sheafificationUnit P := by
    change underlyingPresheafMorphism (forget AddCommGrpCat)
          (abelianSheafificationUnit F) ≫ eGH.hom ≫ eLocal.hom = _
    rw [← Category.assoc, hGH, hp]
  let S : PointwiseAbelianPresheafData H := {
    group := fun U => by
      letI : AddCommGroup (Sections G0 U) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf U
      exact (e.app (op U)).toEquiv.symm.addCommGroup
    restriction_add := by
      intro U V h
      let : AddCommGroup (Sections G0 U) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf U
      let : AddCommGroup (Sections G0 V) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf V
      let := (e.app (op U)).toEquiv.symm.addCommGroup
      let := (e.app (op V)).toEquiv.symm.addCommGroup
      intro s t
      let eU := (e.app (op U)).toEquiv.symm.addEquiv
      let eV := (e.app (op V)).toEquiv.symm.addEquiv
      apply eV.injective
      change eV (restriction h (s + t)) =
        eV (restriction h s + restriction h t)
      rw [map_add]
      have hs := congrArg (fun k => k s) (e.inv.naturality (homOfLE h).op)
      have ht := congrArg (fun k => k t) (e.inv.naturality (homOfLE h).op)
      have hst := congrArg (fun k => k (s + t))
        (e.inv.naturality (homOfLE h).op)
      change eV (restriction h s) =
        (G0.map (homOfLE h).op) (eU s) at hs
      change eV (restriction h t) =
        (G0.map (homOfLE h).op) (eU t) at ht
      change eV (restriction h (s + t)) =
        (G0.map (homOfLE h).op) (eU (s + t)) at hst
      rw [hst, eU.map_add]
      rw [hs, ht]
      exact ((abelianSheafification F).presheaf.map (homOfLE h).op).hom.map_add _ _
    restriction_zero := by
      intro U V h
      let : AddCommGroup (Sections G0 U) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf U
      let : AddCommGroup (Sections G0 V) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf V
      let := (e.app (op U)).toEquiv.symm.addCommGroup
      let := (e.app (op V)).toEquiv.symm.addCommGroup
      let eU := (e.app (op U)).toEquiv.symm.addEquiv
      let eV := (e.app (op V)).toEquiv.symm.addEquiv
      apply eV.injective
      have h0 := congrArg (fun k => k (0 : Sections H U))
        (e.inv.naturality (homOfLE h).op)
      change eV (restriction h 0) =
        (G0.map (homOfLE h).op) (eU 0) at h0
      rw [h0, eU.map_zero, eV.map_zero]
      exact ((abelianSheafification F).presheaf.map (homOfLE h).op).hom.map_zero
    }
  refine ⟨S, ?_, ?_⟩
  · intro U
    let : AddCommGroup (Sections G0 U) :=
      underlyingPresheafAddCommGroup (abelianSheafification F).presheaf U
    let := S.group U
    let eU := (e.app (op U)).toEquiv.symm.addEquiv
    let η : AbelianSections F U →+ Sections H U :=
      eU.symm.toAddMonoidHom.comp
        ((abelianSheafificationUnit F).app (op U)).hom
    refine ⟨η, ?_⟩
    intro s
    have hUs := congrArg (fun k => k.app (op U) s) hcomp
    change (ConcreteCategory.hom (e.hom.app (op U)))
        ((abelianSheafificationUnit F).app (op U) s) =
      (sheafificationUnit P).app (op U) s at hUs
    change (e.app (op U)).hom
        ((abelianSheafificationUnit F).app (op U) s) =
      (sheafificationUnit (underlyingPresheaf F)).app (op U) s
    exact hUs
  · intro T hT
    have unit_restriction :
        ∀ (U V : Opens X) (a : Sections H U) (i : V ⟶ U)
          (σ : (underlyingPresheaf F).obj (op V)),
          (∀ y : V, a.1 (i y) =
            (underlyingPresheaf F).germ V y.1 y.2 σ) →
          H.map i.op a =
            (sheafificationUnit (underlyingPresheaf F)).app (op V) σ := by
      intro U V a i σ ha
      apply Subtype.ext
      funext y
      change a.1 (i y) =
        (underlyingPresheaf F).germ V y.1 y.2 σ
      exact ha y
    have pointwise_ext : ∀ (P Q : PointwiseAbelianPresheafData H),
        P.group = Q.group → P = Q := by
      intro P Q hgroup
      cases P
      cases Q
      cases hgroup
      rfl
    apply pointwise_ext T S
    funext U
    apply AddCommGroup.ext
    change (letI := T.group U; fun s t : Sections H U => s + t) =
      (letI := S.group U; fun s t : Sections H U => s + t)
    funext s t
    apply TopCat.Presheaf.section_ext
      (sheafification (underlyingPresheaf F)) U
    intro x hx
    obtain ⟨V, hxV, iVU, σ, hs⟩ :=
      (sheafificationCondition_iff (underlyingPresheaf F) s.1).mp s.2
        ⟨x, hx⟩
    obtain ⟨W, hxW, iWU, τ, ht⟩ :=
      (sheafificationCondition_iff (underlyingPresheaf F) t.1).mp t.2
        ⟨x, hx⟩
    let Z : Opens X := V ⊓ W
    have hxZ : x ∈ Z := by
      change x ∈ V ∧ x ∈ W
      exact ⟨hxV, hxW⟩
    have hZV : Z ≤ V := by
      dsimp [Z]
      exact inf_le_left
    have hZW : Z ≤ W := by
      dsimp [Z]
      exact inf_le_right
    have hZU : Z ≤ U := hZV.trans iVU.le
    let iZU : Z ⟶ U := homOfLE hZU
    let σZ : (underlyingPresheaf F).obj (op Z) :=
      (underlyingPresheaf F).map (homOfLE hZV).op σ
    let τZ : (underlyingPresheaf F).obj (op Z) :=
      (underlyingPresheaf F).map (homOfLE hZW).op τ
    have hsZ : ∀ y : Z, s.1 (iZU y) =
        (underlyingPresheaf F).germ Z y.1 y.2 σZ := by
      intro y
      let yV : V := ⟨y.1, hZV y.2⟩
      have hs' := hs yV
      calc
        s.1 (iZU y) = s.1 (iVU yV) := by
          congr 1
        _ = (underlyingPresheaf F).germ V y.1 (hZV y.2) σ := by
          simpa [yV] using hs'
        _ = (underlyingPresheaf F).germ Z y.1 y.2 σZ := by
          symm
          simp [σZ]
    have htZ : ∀ y : Z, t.1 (iZU y) =
        (underlyingPresheaf F).germ Z y.1 y.2 τZ := by
      intro y
      let yW : W := ⟨y.1, hZW y.2⟩
      have ht' := ht yW
      calc
        t.1 (iZU y) = t.1 (iWU yW) := by
          congr 1
        _ = (underlyingPresheaf F).germ W y.1 (hZW y.2) τ := by
          simpa [yW] using ht'
        _ = (underlyingPresheaf F).germ Z y.1 y.2 τZ := by
          symm
          simp [τZ]
    have hsZ' : H.map iZU.op s =
        (sheafificationUnit (underlyingPresheaf F)).app (op Z) σZ :=
      unit_restriction U Z s iZU σZ hsZ
    have htZ' : H.map iZU.op t =
        (sheafificationUnit (underlyingPresheaf F)).app (op Z) τZ :=
      unit_restriction U Z t iZU τZ htZ
    have hTsum :
        (letI := T.group U; H.map iZU.op (s + t)) =
          (sheafificationUnit (underlyingPresheaf F)).app (op Z)
            (σZ + τZ) := by
      let : AddCommGroup (Sections H U) := T.group U
      let : AddCommGroup (Sections H Z) := T.group Z
      obtain ⟨ηT, hηT⟩ := hT Z
      calc
        H.map iZU.op (s + t) =
            H.map iZU.op s + H.map iZU.op t := by
          change restriction (F := H) hZU (s + t) =
            restriction (F := H) hZU s + restriction (F := H) hZU t
          exact T.restriction_add hZU s t
        _ = (sheafificationUnit (underlyingPresheaf F)).app (op Z) σZ +
            (sheafificationUnit (underlyingPresheaf F)).app (op Z) τZ := by
          rw [hsZ', htZ']
        _ = ηT σZ + ηT τZ := by
          rw [← hηT σZ, ← hηT τZ]
        _ = ηT (σZ + τZ) := (ηT.map_add σZ τZ).symm
        _ = (sheafificationUnit (underlyingPresheaf F)).app (op Z)
            (σZ + τZ) := hηT _
    have hSsum :
        (letI := S.group U; H.map iZU.op (s + t)) =
          (sheafificationUnit (underlyingPresheaf F)).app (op Z)
            (σZ + τZ) := by
      let : AddCommGroup (Sections G0 U) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf U
      let : AddCommGroup (Sections G0 Z) :=
        underlyingPresheafAddCommGroup (abelianSheafification F).presheaf Z
      let : AddCommGroup (Sections H U) := S.group U
      let : AddCommGroup (Sections H Z) := S.group Z
      let eZ := (e.app (op Z)).toEquiv.symm.addEquiv
      let ηS : AbelianSections F Z →+ Sections H Z :=
        eZ.symm.toAddMonoidHom.comp
          ((abelianSheafificationUnit F).app (op Z)).hom
      have hηS : ∀ a : AbelianSections F Z, ηS a =
          (sheafificationUnit (underlyingPresheaf F)).app (op Z) a := by
        intro a
        have h := congrArg (fun k => k.app (op Z) a) hcomp
        change (ConcreteCategory.hom (e.hom.app (op Z)))
            ((abelianSheafificationUnit F).app (op Z) a) =
          (sheafificationUnit P).app (op Z) a at h
        change (e.app (op Z)).hom
            ((abelianSheafificationUnit F).app (op Z) a) =
          (sheafificationUnit (underlyingPresheaf F)).app (op Z) a
        exact h
      calc
        H.map iZU.op (s + t) =
            H.map iZU.op s + H.map iZU.op t := by
          change restriction (F := H) hZU (s + t) =
            restriction (F := H) hZU s + restriction (F := H) hZU t
          exact S.restriction_add hZU s t
        _ = (sheafificationUnit (underlyingPresheaf F)).app (op Z) σZ +
            (sheafificationUnit (underlyingPresheaf F)).app (op Z) τZ := by
          rw [hsZ', htZ']
        _ = ηS σZ + ηS τZ := by
          rw [← hηS σZ, ← hηS τZ]
        _ = ηS (σZ + τZ) := (ηS.map_add σZ τZ).symm
        _ = (sheafificationUnit (underlyingPresheaf F)).app (op Z)
            (σZ + τZ) := hηS _
    exact H.germ_ext Z hxZ iZU iZU (hTsum.trans hSsum.symm)

/-- The stalk map of the abelian sheafification is an isomorphism. -/
theorem abelianSheafification_stalk_map_isIso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      (abelianSheafificationUnit F)) := by
  apply TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso

/-- The canonical abelian-group isomorphism on stalks. -/
noncomputable def abelianSheafificationStalkIso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (x : X) :
    (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).obj F ≅
      (TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).obj
        (abelianSheafificationPresheaf F) := by
  letI : IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      (abelianSheafificationUnit F)) :=
    abelianSheafification_stalk_map_isIso F x
  exact asIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
    (abelianSheafificationUnit F))

/-- The abelian sheafification Hom equivalence. -/
noncomputable def abelianSheafificationHomEquiv {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (G : TopCat.Sheaf AddCommGrpCat.{v} X) :
    (abelianSheafification F ⟶ G) ≃ (F ⟶ G.presheaf) := by
  change ((CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).obj F ⟶ G) ≃
    (F ⟶ (CategoryTheory.sheafToPresheaf (Opens.grothendieckTopology X)
      AddCommGrpCat).obj G)
  exact (CategoryTheory.sheafificationAdjunction
    (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv F G

/-- The source's adjunction, written from presheaf maps to sheaf maps. -/
noncomputable def abelianSheafificationAdjunctionHomEquiv {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (G : TopCat.Sheaf AddCommGrpCat.{v} X) :
    (F ⟶ G.presheaf) ≃ (abelianSheafification F ⟶ G) :=
  (abelianSheafificationHomEquiv F G).symm

end

end Formalization.Books.Sheaves.Unit17
