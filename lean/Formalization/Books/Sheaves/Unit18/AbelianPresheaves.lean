import Formalization.Books.Sheaves.Unit17.AbelianPresheaves

/-!
# Sheaves on Spaces, Chapter 18: Sheafification of abelian presheaves

The source span is `books/sheaves.tex:1664-1774`.  The preceding chapter
already supplies the canonical `AddCommGrpCat`-valued sheafification, its
stalkwise set presentation, and the four maps in the fibre-product diagram.
This file reuses those declarations through reducible chapter-facing aliases
and adds the source-faithful fixed-carrier uniqueness interface that was not
present there.
-/

namespace Formalization.Books.Sheaves.Unit18

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit11
open Formalization.Books.Sheaves.Unit17

universe v

noncomputable section

/-! ## The canonical abelian sheafification -/

/-- The canonical `AddCommGrpCat`-valued sheafification of an abelian
presheaf. -/
abbrev abelianSheafification {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafification F

/-- The underlying presheaf of the canonical abelian sheafification. -/
abbrev abelianSheafificationPresheaf {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafificationPresheaf F

/-- The canonical additive map from an abelian presheaf to its sheafification. -/
abbrev abelianSheafificationUnit {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafificationUnit F

/-- The underlying set sheaf of the categorical construction agrees with the
stalk-local-germ construction. -/
theorem abelianSheafification_underlying_iso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :
    Nonempty
      (Formalization.Books.Sheaves.Unit05.underlyingPresheaf
          (CategoryTheory.forget AddCommGrpCat) (abelianSheafification F).presheaf ≅
        (sheafification (underlyingPresheaf F)).presheaf) := by
  exact Formalization.Books.Sheaves.Unit17.abelianSheafification_underlying_iso F

/-! ## The fibre-product diagram -/

/-!
The source's fibre-product lemma is stated for an arbitrary set-valued
presheaf.  The four maps below use the canonical local-germ sheafification
and stalk-product presheaves from Chapter 17; the abelian aliases below are
kept for the specialization used in the second lemma.
-/

abbrev fibreProductStalkProduct {X : TopCat.{v}}
    (F : Presheaf X) : TopCat.Presheaf (Type v) X :=
  stalkProductPresheaf F

/-! The top horizontal map `F#(U) → Π(F)(U)`. -/
abbrev fibreProduct_top {X : TopCat.{v}}
    (F : Presheaf X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) ⟶
      (fibreProductStalkProduct F).obj (op U) :=
  (sheafificationProductMap F).app (op U)

/-! The left vertical map `F#(U) → ∏ x∈U Fₓ`. -/
def fibreProduct_left {X : TopCat.{v}}
    (F : Presheaf X) (U : Opens X) :
    (sheafificationPresheaf F).obj (op U) ⟶
      (∀ x : U, F.stalk x) :=
  TypeCat.ofHom (fun s => s.1)

/-! The right vertical map `Π(F)(U) → ∏ x∈U Π(F)ₓ`. -/
abbrev fibreProduct_right {X : TopCat.{v}}
    (F : Presheaf X) (U : Opens X) :
    (fibreProductStalkProduct F).obj (op U) ⟶
      (∀ x : U, (fibreProductStalkProduct F).stalk x) :=
  (presheafToStalkProduct (fibreProductStalkProduct F)).app (op U)

/-! The bottom horizontal map, componentwise induced by `Fₓ → Π(F)ₓ`. -/
def fibreProduct_bottom {X : TopCat.{v}}
    (F : Presheaf X) (U : Opens X) :
    (∀ x : U, F.stalk x) ⟶
      (∀ x : U, (fibreProductStalkProduct F).stalk x) :=
  TypeCat.ofHom (fun s x =>
    (TopCat.Presheaf.stalkFunctor (Type v) x.1).map
      (presheafToStalkProduct F) (s x))

/-! The source's four-corner diagram is a pullback in `Type`. -/
theorem sheafification_fibreProduct {X : TopCat.{v}}
    (F : Presheaf X) (U : Opens X) :
    IsPullback (fibreProduct_top F U) (fibreProduct_left F U)
      (fibreProduct_right F U) (fibreProduct_bottom F U) := by
  exact Formalization.Books.Sheaves.Unit17.sheafification_fibreProduct F U

/-! ## The abelian specialization of the four maps -/

/-- The presheaf of all stalkwise sections `Π(F)`. -/
abbrev abelianFibreProductStalkProduct {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianFibreProductStalkProduct F

/-- The top horizontal map `F#(U) → Π(F)(U)`. -/
abbrev abelianFibreProduct_top {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :=
  Formalization.Books.Sheaves.Unit17.abelianFibreProduct_top F U

/-- The left vertical map `F#(U) → ∏ x∈U Fₓ`. -/
abbrev abelianFibreProduct_left {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :=
  Formalization.Books.Sheaves.Unit17.abelianFibreProduct_left F U

/-- The right vertical map `Π(F)(U) → ∏ x∈U Π(F)ₓ`. -/
abbrev abelianFibreProduct_right {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :=
  Formalization.Books.Sheaves.Unit17.abelianFibreProduct_right F U

/-- The bottom horizontal map, componentwise induced by `Fₓ → Π(F)ₓ`. -/
abbrev abelianFibreProduct_bottom {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :=
  Formalization.Books.Sheaves.Unit17.abelianFibreProduct_bottom F U

/-- The source's four-corner diagram is a pullback in `Type`. -/
theorem abelianSheafification_fibreProduct {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    IsPullback (abelianFibreProduct_top F U) (abelianFibreProduct_left F U)
      (abelianFibreProduct_right F U) (abelianFibreProduct_bottom F U) := by
  exact Formalization.Books.Sheaves.Unit17.abelianSheafification_fibreProduct F U

/-! ## The unique abelian structure and its stalk consequence -/

/-!
`PointwiseAbelianPresheafData` is the earlier chapter's fixed-carrier
presentation of a presheaf of abelian groups.  The predicate below says that
the canonical unit is additive at every open; naturality and the additive
restriction laws are already fields of that established interface.
-/

/-- A pointwise abelian-sheaf structure on the fixed set-valued sheaf `F#`
for which the unit `F → F#` is additive. -/
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
  exact Formalization.Books.Sheaves.Unit17.existsUnique_abelianSheafificationStructure F

/-- The canonical abelian-group stalk map of the sheafification is an
isomorphism, expressing the source's identification `Fₓ ≅ F#ₓ`. -/
theorem abelianSheafification_stalk_map_isIso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      (abelianSheafificationUnit F)) := by
  exact Formalization.Books.Sheaves.Unit17.abelianSheafification_stalk_map_isIso F x

/-- The canonical abelian-group isomorphism on stalks. -/
noncomputable abbrev abelianSheafificationStalkIso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (x : X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafificationStalkIso F x

/-! ## The adjointness property -/

/-- The abelian sheafification Hom equivalence. -/
noncomputable abbrev abelianSheafificationHomEquiv {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (G : TopCat.Sheaf AddCommGrpCat.{v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafificationHomEquiv F G

/-- The source's adjunction, written from presheaf maps to sheaf maps. -/
noncomputable abbrev abelianSheafificationAdjunctionHomEquiv {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (G : TopCat.Sheaf AddCommGrpCat.{v} X) :=
  Formalization.Books.Sheaves.Unit17.abelianSheafificationAdjunctionHomEquiv F G

end

end Formalization.Books.Sheaves.Unit18
