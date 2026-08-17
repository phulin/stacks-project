import Formalization.Books.Sheaves.Unit12.StalksOfAbelianPresheaves
import Formalization.Books.Sheaves.Unit17.Sheafification
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
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
  sorry

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
  sorry

/-- The source's four-corner diagram is a pullback in `Type`. -/
theorem abelianSheafification_fibreProduct {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (U : Opens X) :
    IsPullback (abelianFibreProduct_top F U) (abelianFibreProduct_left F U)
      (abelianFibreProduct_right F U) (abelianFibreProduct_bottom F U) := by
  sorry

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
  sorry

/-- The stalk map of the abelian sheafification is an isomorphism. -/
theorem abelianSheafification_stalk_map_isIso {X : TopCat.{v}}
    (F : AbelianPresheaf.{v, v} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor (AddCommGrpCat.{v}) x).map
      (abelianSheafificationUnit F)) := by
  sorry

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
