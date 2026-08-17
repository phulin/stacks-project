import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Topology.Bases
import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
import Mathlib.Topology.Category.TopCat.Limits.Konig
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Topology, Chapter 14: Limits of spaces

The category-theoretic statements use Mathlib's `TopCat`, `Cone`, and
`IsLimit` APIs.  The concrete equalizer construction is recorded as a bridge
to the source's subtype description; the canonical categorical equalizer is
then related to it by a unique isomorphism.
 -/

namespace Formalization.Books.Topology.Unit14

open CategoryTheory CategoryTheory.Limits
open Set TopologicalSpace

universe u v w

noncomputable section

section ProductsAndEqualizers

variable {X Y : TopCat.{u}}

/- The canonical `TopCat` instance supplies the product assertion in the
   source.  The following basis theorem records the source's concrete
   description of the product topology. -/

def product_fan_is_limit {ι : Type v} (X : ι → TopCat.{max v u}) :
    IsLimit (TopCat.piFan X) :=
  TopCat.piFanIsLimit X

theorem topological_spaces_have_products :
    HasProducts.{u} (TopCat.{u}) := by
  infer_instance

theorem product_topology_basis {ι : Type v} {X : ι → Type u}
    [∀ i, TopologicalSpace (X i)] :
    IsTopologicalBasis
      {S : Set (∀ i, X i) |
        ∃ (U : ∀ i, Set (X i)) (F : Finset ι),
          (∀ i, i ∈ F → IsOpen (U i)) ∧ S = (F : Set ι).pi U} := by
  simpa using (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens))

/- The subtype below has the induced topology inherited from `X`, exactly as
   in the source's concrete equalizer construction. -/

def equalizerSubtype (f g : X ⟶ Y) : TopCat.{u} :=
  TopCat.of {x : X // f x = g x}

def equalizerSubtypeInclusion (f g : X ⟶ Y) : equalizerSubtype f g ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def equalizerSubtypeFork (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (equalizerSubtypeInclusion f g) (by
    apply TopCat.ext
    intro x
    change f x.1 = g x.1
    exact x.property)

def equalizerSubtypeForkIsLimit (f g : X ⟶ Y) :
    IsLimit (equalizerSubtypeFork f g) :=
  Fork.IsLimit.mk' _ (fun S =>
    ⟨TopCat.ofHom
        { toFun := fun x =>
            ⟨S.ι x, ConcreteCategory.congr_hom S.condition x⟩
          continuous_toFun :=
            Continuous.subtype_mk S.ι.hom.2
              (fun x => ConcreteCategory.congr_hom S.condition x) },
      by
        apply TopCat.ext
        intro x
        rfl,
      fun h => by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        exact ConcreteCategory.congr_hom h x⟩)

noncomputable def equalizerIsoSubtype (f g : X ⟶ Y) :
    equalizer f g ≅ equalizerSubtype f g :=
  (limit.isLimit (parallelPair f g)).conePointUniqueUpToIso
    (equalizerSubtypeForkIsLimit f g)

theorem topological_spaces_have_equalizers :
    HasEqualizers (TopCat.{u}) := by
  infer_instance

end ProductsAndEqualizers

section Limits

theorem topological_spaces_have_limits :
    HasLimits (TopCat.{u}) := by
  infer_instance

theorem topological_space_forgetful_preserves_limits :
    PreservesLimits (CategoryTheory.forget (TopCat.{u})) := by
  infer_instance

end Limits

section CofilteredLimits

variable {J : Type v} [Category.{w} J] [IsCofiltered J]

/- Mathlib's stronger basis theorem is specialized here to the basis of open
   subsets used in the source. -/

theorem cofiltered_limit_open_preimage_basis
    (F : J ⥤ TopCat.{max v u}) :
    IsTopologicalBasis
      {U : Set ((limit F : TopCat.{max v u}) : Type (max v u)) |
        ∃ (j : J) (V : Set (F.obj j)),
          IsOpen V ∧ U = (limit.π F j) ⁻¹' V} := by
  let T : ∀ j : J, Set (Set (F.obj j)) := fun _ => {V | IsOpen V}
  have hT : ∀ j, IsTopologicalBasis (T j) := by
    intro j
    simpa [T] using (isTopologicalBasis_opens : IsTopologicalBasis {V : Set (F.obj j) | IsOpen V})
  have huniv : ∀ i : J, Set.univ ∈ T i := by
    intro i
    exact isOpen_univ
  have hinter : ∀ (i : J) (U₁ U₂ : Set (F.obj i)), U₁ ∈ T i → U₂ ∈ T i →
      U₁ ∩ U₂ ∈ T i := by
    intro i U₁ U₂ hU₁ hU₂
    exact hU₁.inter hU₂
  have hcompat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (_hV : V ∈ T j),
      F.map f ⁻¹' V ∈ T i := by
    intro i j f V hV
    exact hV.preimage (F.map f).hom.2
  simpa [T] using
    (TopCat.isTopologicalBasis_cofiltered_limit.{u, v, w} (F := F) (C := limit.cone F)
      (limit.isLimit F) T hT huniv hinter hcompat)

theorem cofiltered_limit_open_eq_iUnion
    (F : J ⥤ TopCat.{max v u})
    {W : Set ((limit F : TopCat.{max v u}) : Type (max v u))} (hW : IsOpen W) :
    ∃ (S : Set J) (U : ∀ j : J, Set (F.obj j)),
      (∀ j, j ∈ S → IsOpen (U j)) ∧
        W = ⋃ j ∈ S, (limit.π F j) ⁻¹' U j := by
  sorry

theorem cofiltered_limit_quasiCompact_open_eq_preimage
    (F : J ⥤ TopCat.{max v u})
    {W : Set ((limit F : TopCat.{max v u}) : Type (max v u))}
    (hWopen : IsOpen W) (hWcompact : IsCompact W) :
    ∃ (j : J) (V : Set (F.obj j)),
      IsOpen V ∧ W = (limit.π F j) ⁻¹' V := by
  sorry

noncomputable def isLimit_of_set_limit_of_open_preimage_basis
    {F : J ⥤ TopCat.{u}} (C : Cone F)
    (hset : IsLimit ((CategoryTheory.forget (TopCat.{u})).mapCone C))
    (hbasis :
      IsTopologicalBasis
        {U : Set C.pt |
          ∃ (j : J) (V : Set (F.obj j)),
            IsOpen V ∧ U = (C.π.app j) ⁻¹' V}) :
    IsLimit C := by
  classical
  exact Classical.choice ((TopCat.nonempty_isLimit_iff_eq_induced C hset).2 (by
    apply le_antisymm
    · refine le_iInf fun j => ?_
      exact continuous_iff_le_induced.mp (C.π.app j).hom.2
    · rw [hbasis.eq_generateFrom]
      apply le_generateFrom
      rintro U ⟨j, V, hV, rfl⟩
      exact (isOpen_induced (f := C.π.app j) hV).mono (iInf_le _ j)))

end CofilteredLimits

section Compactness

variable {ι : Type v} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

theorem tychonoff [∀ i, CompactSpace (X i)] :
    CompactSpace (∀ i, X i) := by
  infer_instance

theorem compactSpace_limit_of_compact_Hausdorff
    {J : Type v} [Category.{w} J] (F : J ⥤ TopCat.{u}) [HasLimit F]
    [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)] :
    CompactSpace ((limit F : TopCat.{u}) : Type u) := by
  sorry

/- The source explicitly warns that the preceding compactness conclusion is
   false without the Hausdorff assumptions.  Those assumptions are therefore
   retained in the theorem interface; the source points to an external
   counterexample rather than specifying one in this section. -/

end Compactness

section NonemptyLimits

variable {J : Type u} [SmallCategory J] [IsCofiltered J]

theorem nonempty_cofiltered_limit_of_compact_Hausdorff
    (F : J ⥤ TopCat.{max v u})
    [∀ j, Nonempty (F.obj j)] [∀ j, CompactSpace (F.obj j)]
    [∀ j, T2Space (F.obj j)] :
    Nonempty ((limit F : TopCat.{max v u}) : Type (max v u)) := by
  obtain ⟨x⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system F
  let e := (TopCat.limitConeIsLimit F).conePointUniqueUpToIso (limit.isLimit F)
  exact ⟨e.hom x⟩

end NonemptyLimits

end

end Formalization.Books.Topology.Unit14
