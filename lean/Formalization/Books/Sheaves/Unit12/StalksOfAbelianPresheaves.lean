import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit11.Stalks
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Sheaves on Spaces, Chapter 12: Stalks of abelian presheaves

The source span `books/sheaves.tex:1050-1088` is the section
`Stalks of abelian presheaves`.  Abelian presheaves use the canonical
`AddCommGrpCat`-valued presheaves from Chapter 4, and their stalks use
Mathlib's filtered colimits.  The underlying set-valued stalk is related to
the canonical abelian-group-valued stalk by the preservation of filtered
colimits by the forgetful functor.
-/

namespace Formalization.Books.Sheaves.Unit12

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit11

universe u

noncomputable section

/-! ## The abelian-group structure on a stalk -/

/-- The stalk of an abelian presheaf, computed in `AddCommGrpCat`. -/
abbrev AbelianStalk {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk F x

/-- The underlying set of the stalk of an abelian presheaf. -/
abbrev AbelianStalkAsSet {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :=
  Stalk (underlyingPresheaf F) x

/-- The canonical equivalence between the set-valued stalk and the underlying
type of the `AddCommGrpCat`-valued stalk. -/
def abelianStalkUnderlyingEquiv
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    AbelianStalkAsSet F x ≃ ToType (AbelianStalk F x) :=
  (preservesColimitIso (forget AddCommGrpCat)
      ((OpenNhds.inclusion x).op ⋙ F)).symm.toEquiv

/-- The canonical abelian-group structure transported to the set-valued stalk. -/
@[instance_reducible]
def abelianStalkAddCommGroup
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    AddCommGroup (AbelianStalkAsSet F x) := by
  letI : AddCommGroup (ToType (AbelianStalk F x)) := AddCommGrpCat.str _
  exact (abelianStalkUnderlyingEquiv F x).addCommGroup

/-- A group structure on the stalk is compatible with the germ maps when every
germ map is an additive homomorphism. -/
def IsAbelianStalkGroupStructure
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X)
    (G : AddCommGroup (AbelianStalkAsSet F x)) : Prop :=
  ∀ (U : Opens X) (hx : x ∈ U),
    letI := G
    ∃ φ : AbelianSections F U →+ AbelianStalkAsSet F x,
      ∀ s, φ s = germApply (F := underlyingPresheaf F) U x hx s

/-- The canonical group structure on the underlying stalk satisfies the germ
compatibility condition. -/
theorem abelianStalkAddCommGroup_isStructure
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    IsAbelianStalkGroupStructure F x (abelianStalkAddCommGroup F x) := by
  sorry

/-- Any group structure on the stalk for which all germ maps are homomorphisms
is the canonical transported structure. -/
theorem abelianStalkAddCommGroup_eq_canonical
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X)
    (G : AddCommGroup (AbelianStalkAsSet F x))
    (hG : IsAbelianStalkGroupStructure F x G) :
    G = abelianStalkAddCommGroup F x := by
  sorry

/-- There is a unique abelian-group structure on the stalk making all germ maps
from sections into additive homomorphisms. -/
theorem existsUnique_abelianStalkAddCommGroup
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    ∃! G : AddCommGroup (AbelianStalkAsSet F x),
      IsAbelianStalkGroupStructure F x G := by
  refine ⟨abelianStalkAddCommGroup F x,
    abelianStalkAddCommGroup_isStructure F x, ?_⟩
  intro G hG
  exact abelianStalkAddCommGroup_eq_canonical F x G hG

/-! ## The filtered-colimit presentation -/

/-- The canonical cocone defining the abelian-group-valued stalk. -/
def abelianStalkCocone
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ F) :=
  colimit.cocone ((OpenNhds.inclusion x).op ⋙ F)

@[simp]
theorem abelianStalk_eq_colimit
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    AbelianStalk F x = colimit ((OpenNhds.inclusion x).op ⋙ F) :=
  rfl

/-- The stalk cocone is a colimit in the category of abelian groups. -/
noncomputable def abelianStalkCocone_is_colimit
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X) :
    IsColimit (abelianStalkCocone F x) :=
  colimit.isColimit _

/-! ## Directed neighborhoods and coproducts -/

/-- The open neighborhoods of a point form a directed partially ordered set. -/
theorem openNhds_is_directed (X : TopCat.{u}) (x : X) :
    IsDirectedOrder (OpenNhds x) := by
  infer_instance

/-- In `AddCommGrpCat`, the binary coproduct is canonically the direct-sum
biproduct. -/
def abelianBinaryCoproductIsoDirectSum (A B : AddCommGrpCat.{u}) :
    Limits.coprod A B ≅ A ⊞ B :=
  (biprod.isoCoprod A B).symm

/-- In `Type`, the binary coproduct is canonically the disjoint union. -/
def setBinaryCoproductIsoDisjointUnion (A B : Type u) :
    Limits.coprod A B ≅ A ⊕ B :=
  Types.binaryCoproductIso A B

/-- The forgetful functor from abelian groups to sets does not preserve all
binary coproducts. -/
theorem forget_addCommGrpCat_not_preserves_binary_coproduct :
    ¬ PreservesColimit
      (pair (AddCommGrpCat.of (PUnit : Type u))
        (AddCommGrpCat.of (PUnit : Type u)))
      (forget AddCommGrpCat.{u}) := by
  sorry

end

end Formalization.Books.Sheaves.Unit12
