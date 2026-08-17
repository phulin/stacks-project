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
  intro U hx
  let e := abelianStalkUnderlyingEquiv F x
  let : AddCommGroup (AbelianStalkAsSet F x) := e.addCommGroup
  let φ : AbelianSections F U →+ AbelianStalkAsSet F x :=
    (e.addEquiv).symm.toAddMonoidHom.comp (F.germ U x hx).hom
  refine ⟨φ, ?_⟩
  intro s
  let j : (OpenNhds x)ᵒᵖ := op (⟨U, hx⟩ : OpenNhds x)
  have h := ι_preservesColimitIso_hom (forget AddCommGrpCat)
    ((OpenNhds.inclusion x).op ⋙ F) j
  change (ConcreteCategory.hom
      (preservesColimitIso (forget AddCommGrpCat)
        ((OpenNhds.inclusion x).op ⋙ F)).hom)
      ((ConcreteCategory.hom ((forget AddCommGrpCat).map
        (colimit.ι ((OpenNhds.inclusion x).op ⋙ F) j))) s) =
    (ConcreteCategory.hom
      (colimit.ι (((OpenNhds.inclusion x).op ⋙ F) ⋙ forget AddCommGrpCat) j)) s
  have h' := congrArg (fun k => (ConcreteCategory.hom k) s) h
  change (ConcreteCategory.hom
      (preservesColimitIso (forget AddCommGrpCat)
        ((OpenNhds.inclusion x).op ⋙ F)).hom)
      ((ConcreteCategory.hom ((forget AddCommGrpCat).map
        (colimit.ι ((OpenNhds.inclusion x).op ⋙ F) j))) s) =
    (ConcreteCategory.hom
      (colimit.ι (((OpenNhds.inclusion x).op ⋙ F) ⋙ forget AddCommGrpCat) j)) s at h'
  exact h'

/-- Any group structure on the stalk for which all germ maps are homomorphisms
is the canonical transported structure. -/
theorem abelianStalkAddCommGroup_eq_canonical
    {X : TopCat.{u}} (F : AbelianPresheaf.{u, u} X) (x : X)
    (G : AddCommGroup (AbelianStalkAsSet F x))
    (hG : IsAbelianStalkGroupStructure F x G) :
    G = abelianStalkAddCommGroup F x := by
  apply AddCommGroup.ext
  funext a b
  obtain ⟨U, hxU, s, hs⟩ := (underlyingPresheaf F).exists_germ_eq a
  obtain ⟨V, hxV, t, ht⟩ := (underlyingPresheaf F).exists_germ_eq b
  let W := U ⊓ V
  have hxW : x ∈ W := by
    simp [W, hxU, hxV]
  let : AddCommGroup (AbelianSections F W) := AddCommGrpCat.str _
  let sW : AbelianSections F W :=
    (F.map (homOfLE (show W ≤ U from by simp [W])).op).hom s
  let tW : AbelianSections F W :=
    (F.map (homOfLE (show W ≤ V from by simp [W])).op).hom t
  have hsW : germApply (F := underlyingPresheaf F) W x hxW sW = a := by
    rw [← hs]
    exact (underlyingPresheaf F).germ_res_apply _ x hxW s
  have htW : germApply (F := underlyingPresheaf F) W x hxW tW = b := by
    rw [← ht]
    exact (underlyingPresheaf F).germ_res_apply _ x hxW t
  obtain ⟨φG, hφG⟩ := hG W hxW
  obtain ⟨φC, hφC⟩ := abelianStalkAddCommGroup_isStructure F x W hxW
  have hGadd :
      (letI := G; φG (sW + tW)) =
        (letI := G; φG sW + φG tW) :=
    φG.map_add sW tW
  let : AddCommGroup (AbelianStalkAsSet F x) := abelianStalkAddCommGroup F x
  have hCadd :
      (letI := abelianStalkAddCommGroup F x; φC (sW + tW)) =
        (letI := abelianStalkAddCommGroup F x; φC sW + φC tW) :=
    φC.map_add sW tW
  rw [← hsW, ← htW]
  calc
    (letI := G; germApply (F := underlyingPresheaf F) W x hxW sW +
        germApply (F := underlyingPresheaf F) W x hxW tW) =
      (letI := G; φG sW + φG tW) := by rw [hφG, hφG]
    _ = (letI := G; φG (sW + tW)) := hGadd.symm
    _ = germApply (F := underlyingPresheaf F) W x hxW (sW + tW) := hφG _
    _ = φC (sW + tW) := (hφC _).symm
    _ = (letI := abelianStalkAddCommGroup F x; φC sW + φC tW) := hCadd
    _ = (letI := abelianStalkAddCommGroup F x;
      germApply (F := underlyingPresheaf F) W x hxW sW +
        germApply (F := underlyingPresheaf F) W x hxW tW) := by
      rw [hφC, hφC]

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

/-- The reverse-inclusion order on the open neighborhoods of a point is
directed, as used by the stalk colimit. -/
theorem openNhds_is_directed (X : TopCat.{u}) (x : X) :
    IsDirectedOrder (OpenNhds x)ᵒᵈ := by
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

/-- The forgetful functor from abelian groups to sets does not preserve the
displayed binary coproduct. -/
theorem forget_addCommGrpCat_not_preserves_binary_coproduct :
    ¬ PreservesColimit
      (pair (AddCommGrpCat.of (PUnit : Type u))
        (AddCommGrpCat.of (PUnit : Type u)))
      (forget AddCommGrpCat.{u}) := by
  intro h
  let A : AddCommGrpCat.{u} := AddCommGrpCat.of (PUnit : Type u)
  let c : BinaryCofan A A :=
    BinaryCofan.mk
      (coprod.inl : A ⟶ A ⨿ A) coprod.inr
  have hc : IsColimit ((forget AddCommGrpCat).mapCocone c) :=
    (h.preserves (coprodIsCoprod A A)).some
  have hc' : IsColimit (c.map (forget AddCommGrpCat)) :=
    (BinaryCofan.isColimitMapConeEquiv (F := forget AddCommGrpCat) (s := c)) hc
  have hiff := (Types.binaryCofan_isColimit_iff (c.map (forget AddCommGrpCat))).mp ⟨hc'⟩
  apply Set.disjoint_left.1 hiff.2.2.disjoint
  · exact ⟨PUnit.unit, rfl⟩
  · refine ⟨PUnit.unit, ?_⟩
    change c.inr.hom PUnit.unit = c.inl.hom PUnit.unit
    have hu : (PUnit.unit : ToType A) = 0 := by rfl
    calc
      c.inr.hom PUnit.unit = c.inr.hom 0 := congrArg c.inr.hom hu
      _ = 0 := c.inr.hom.map_zero
      _ = c.inl.hom 0 := (c.inl.hom.map_zero).symm
      _ = c.inl.hom PUnit.unit := congrArg c.inl.hom hu.symm

end

end Formalization.Books.Sheaves.Unit12
