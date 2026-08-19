import Formalization.Books.Categories.Unit23.ExactFunctors
import Formalization.Books.Categories.Unit24.AdjointFunctors
import Formalization.Books.Sheaves.Unit08.AbelianSheaves
import Formalization.Books.Sheaves.Unit21.ContinuousMaps
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks

/-!
# Sheaves on Spaces, Chapter 32: Closed immersions and (pre)sheaves

The source section is `books/sheaves.tex:4925-5070`.  The inclusion of a
closed subset is represented by the canonical subtype inclusion in `TopCat`,
and pushforward, pullback, stalks, essential images, and exactness use the
corresponding Mathlib and earlier-chapter interfaces.

The source's later abelian-sheaf result and its ringed-space scope remark are
recorded as documentation only.  Their constructions and results belong to
later material, so they are not moved into this chapter by artificial
declarations.
-/

namespace Formalization.Books.Sheaves.Unit32

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped ZeroObject
open Formalization.Books.Categories.Unit23
open Formalization.Books.Sheaves.Unit07
open Formalization.Books.Sheaves.Unit08
open Formalization.Books.Sheaves.Unit21

universe u v w

noncomputable section

/- Mathlib's site-level colimit instance is stated for
   `CategoryTheory.Sheaf`, while `TopCat.Sheaf` is its canonical topological
   specialization introduced by a reducible definition.  This small bridge
   exposes the existing site-level finite-colimit API at the specialization;
   no new colimit construction is introduced here. -/
noncomputable instance topCatSheaf_hasFiniteColimits
    {C : Type u} [Category.{v} C] [HasFiniteColimits C]
    (X : TopCat.{w})
    [HasWeakSheafify (Opens.grothendieckTopology X) C] :
    HasFiniteColimits (TopCat.Sheaf C X) := by sorry
def closedSubsetInclusion {X : TopCat.{w}} (Z : Set X) : TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The subtype inclusion is a closed embedding when the subset is closed. -/
theorem closedSubsetInclusion_isClosedEmbedding {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) : IsClosedEmbedding (closedSubsetInclusion Z) := by sorry
abbrev closedSubsetPushforward {C : Type u} [Category.{v} C]
    {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf C (TopCat.of Z) ⥤ TopCat.Sheaf C X :=
  TopCat.Sheaf.pushforward C (closedSubsetInclusion Z)

/-- Set-valued pushforward along the closed subset inclusion. -/
abbrev closedSubsetSetPushforward {X : TopCat.{w}} (Z : Set X) :
    Sh.{w, w} (TopCat.of Z) ⥤ Sh.{w, w} X :=
  pushforwardSheaf (closedSubsetInclusion Z)

/-- Set-valued pullback along the closed subset inclusion. -/
noncomputable abbrev closedSubsetSetPullback {X : TopCat.{w}} (Z : Set X) :
    Sh.{w, w} X ⥤ Sh.{w, w} (TopCat.of Z) :=
  pullbackSheaf (closedSubsetInclusion Z)

/-- The set-valued pullback/pushforward adjunction. -/
noncomputable abbrev closedSubsetSetAdjunction {X : TopCat.{w}} (Z : Set X) :
    closedSubsetSetPullback Z ⊣ closedSubsetSetPushforward Z :=
  pullbackSheafPushforwardAdjunction (closedSubsetInclusion Z)

/-! ## Stalks and the counit -/

/- The following is the canonical stalk comparison at a point of the closed
   subset.  It has a real body: the comparison is the Mathlib
   `stalkPushforward` map, which is an isomorphism for an inducing map. -/

/-- The pushforward stalk at a point of the subset is the original stalk. -/
noncomputable def closedSubsetPushforward_stalkIso
    {C : Type u} [Category.{w} C] [HasColimits C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (TopCat.of Z)) (z : Z) :
    TopCat.Presheaf.stalk (C := C) (X := X)
        ((closedSubsetPushforward (C := C) Z).obj F).presheaf
        (closedSubsetInclusion Z z) ≅
      TopCat.Presheaf.stalk (C := C) (X := TopCat.of Z) F.presheaf z := by sorry
theorem closedSubsetPushforward_stalkIso_terminal_of_not_mem
    {C : Type u} [Category.{w} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf C (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (TopCat.Presheaf.stalk (C := C) (X := X)
      ((closedSubsetPushforward (C := C) Z).obj F).presheaf x ≅ (⊤_ C)) := by sorry
theorem closedSubsetSetPushforward_stalk_equiv_punit_of_not_mem
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sh.{w, w} (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSubsetSetPushforward Z).obj F).presheaf.stalk x ≃
      (PUnit : Type w)) := by sorry
noncomputable def closedSubsetSetPushforward_stalkEquiv
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : Sh.{w, w} (TopCat.of Z)) (z : Z) :
    TopCat.Presheaf.stalk (C := Type w) (X := X)
        ((closedSubsetSetPushforward Z).obj F).presheaf
        (closedSubsetInclusion Z z) ≃
      TopCat.Presheaf.stalk (C := Type w) (X := TopCat.of Z) F.presheaf z :=
  (closedSubsetPushforward_stalkIso (C := Type w) hZ F z).toEquiv

private theorem closedSubsetPushforward_counit_isIso_of_category
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso ((TopCat.Sheaf.pullbackPushforwardAdjunction C
      (closedSubsetInclusion Z)).counit) := by sorry
theorem closedSubsetSet_inverseImage_pushforward_counit_isIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso (closedSubsetSetAdjunction Z |>.counit) := by sorry
noncomputable def closedSubsetSet_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetSetPushforward Z ⋙ closedSubsetSetPullback Z ≅
      𝟭 (Sh.{w, w} (TopCat.of Z)) := by sorry
abbrev closedSubsetSet_terminalStalkCondition
    {X : TopCat.{w}} (Z : Set X) (G : Sh.{w, w} X) : Prop :=
  ∀ x : X, x ∉ Z → Nonempty (G.presheaf.stalk x ≃ (PUnit : Type w))

/-- Pushforward along a closed subset inclusion is fully faithful for sets. -/
theorem closedSubsetSetPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetSetPushforward Z).FullyFaithful := by sorry
theorem closedSubsetSetPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) (G : Sh.{w, w} X) :
    (closedSubsetSetPushforward Z).essImage G ↔
      closedSubsetSet_terminalStalkCondition Z G := by sorry
abbrev closedSubsetAbelianPushforward {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z) ⥤
      TopCat.Sheaf AddCommGrpCat.{w} X :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{w} (closedSubsetInclusion Z)

/-- Pullback of abelian sheaves along the closed subset inclusion. -/
noncomputable abbrev closedSubsetAbelianPullback {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf AddCommGrpCat.{w} X ⥤
      TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z) :=
  TopCat.Sheaf.pullback AddCommGrpCat.{w} (closedSubsetInclusion Z)

/-- The abelian sheaf pullback/pushforward adjunction. -/
noncomputable abbrev closedSubsetAbelianAdjunction {X : TopCat.{w}} (Z : Set X) :
    closedSubsetAbelianPullback Z ⊣ closedSubsetAbelianPushforward Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{w}
    (closedSubsetInclusion Z)

/-- The outside stalk of an abelian pushforward is isomorphic to zero. -/
theorem closedSubsetAbelianPushforward_stalkIso_zero_of_not_mem
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) {x : X} (hx : x ∉ Z) :
    Nonempty (((closedSubsetAbelianPushforward Z).obj F).presheaf.stalk x ≅
      (0 : AddCommGrpCat.{w})) := by sorry
noncomputable def closedSubsetAbelianPushforward_stalkIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (F : TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) (z : Z) :
    ((closedSubsetAbelianPushforward Z).obj F).presheaf.stalk
        (closedSubsetInclusion Z z) ≅ F.presheaf.stalk z :=
  closedSubsetPushforward_stalkIso (C := AddCommGrpCat.{w}) hZ F z

/-- The abelian sheaf counit is an isomorphism. -/
theorem closedSubsetAbelian_inverseImage_pushforward_counit_isIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso (closedSubsetAbelianAdjunction Z |>.counit) := by sorry
noncomputable def closedSubsetAbelian_inverseImagePushforwardIso
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetAbelianPushforward Z ⋙ closedSubsetAbelianPullback Z ≅
      𝟭 (TopCat.Sheaf AddCommGrpCat.{w} (TopCat.of Z)) := by sorry
abbrev closedSubsetAbelian_zeroStalkCondition
    {X : TopCat.{w}} (Z : Set X)
    (G : TopCat.Sheaf AddCommGrpCat.{w} X) : Prop :=
  ∀ x : X, x ∉ Z →
    Nonempty (TopCat.Presheaf.stalk (C := AddCommGrpCat.{w}) (X := X)
      G.presheaf x ≅ (0 : AddCommGrpCat.{w}))

/-- Pushforward along a closed subset inclusion is fully faithful for abelian sheaves. -/
theorem closedSubsetAbelianPushforward_fullyFaithful
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetAbelianPushforward Z).FullyFaithful := by sorry
private noncomputable def closedSubsetPullbackStalkIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X}
    (G : TopCat.Sheaf C X) (z : Z) :
    G.presheaf.stalk (closedSubsetInclusion Z z) ≅
      ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G).presheaf.stalk z := by sorry
private lemma category_comp_iso_inv_hom_cancel
    {C : Type u} [Category.{w} C]
    {A B D E F : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (e : F ≅ E) :
    (f ≫ g ≫ h ≫ e.inv) ≫ e.hom = f ≫ g ≫ h := by sorry
private theorem closedSubsetPushforward_unit_stalk_comp
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) (z : Z) :
    (TopCat.Presheaf.stalkFunctor (C := C) (X := X)
        (closedSubsetInclusion Z z)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction C
          (closedSubsetInclusion Z)).unit.app G).hom ≫
    (closedSubsetPushforward_stalkIso (C := C) hZ
        ((TopCat.Sheaf.pullback C (closedSubsetInclusion Z)).obj G) z).hom =
    (closedSubsetPullbackStalkIso G z).hom := by sorry
private theorem closedSubsetPushforward_mem_essImage_iff_of_category
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [HasTerminal C]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) :
    (closedSubsetPushforward (C := C) Z).essImage G ↔
      ∀ x : X, x ∉ Z →
        Nonempty (TopCat.Presheaf.stalk (C := C) G.presheaf x ≅ (⊤_ C)) := by sorry
theorem closedSubsetAbelianPushforward_mem_essImage_iff
    {X : TopCat.{w}} {Z : Set X}
    (hZ : IsClosed Z) (G : TopCat.Sheaf AddCommGrpCat.{w} X) :
    (closedSubsetAbelianPushforward Z).essImage G ↔
      closedSubsetAbelian_zeroStalkCondition Z G := by sorry
noncomputable abbrev closedSubsetStructurePullback
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} (Z : Set X) :
    TopCat.Sheaf C X ⥤ TopCat.Sheaf C (TopCat.of Z) :=
  TopCat.Sheaf.pullback C (closedSubsetInclusion Z)

/-- The generic sheaf pullback/pushforward adjunction for a closed subset. -/
noncomputable abbrev closedSubsetStructureAdjunction
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} (Z : Set X) :
    closedSubsetStructurePullback (C := C) Z ⊣ closedSubsetPushforward (C := C) Z :=
  TopCat.Sheaf.pullbackPushforwardAdjunction C (closedSubsetInclusion Z)

/-- Generic terminal-stalk condition for sheaves of algebraic structures. -/
abbrev closedSubsetTerminalStalkCondition
    {C : Type u} [Category.{w} C] [HasColimits C] [HasTerminal C]
    {X : TopCat.{w}}
    (Z : Set X) (G : TopCat.Sheaf C X) : Prop :=
  ∀ x : X, x ∉ Z →
    Nonempty (TopCat.Presheaf.stalk (C := C) (X := X) G.presheaf x ≅ (⊤_ C))

/-- Generic counit form of `i⁻¹ i_* ≅ id` for algebraic-structure sheaves. -/
theorem closedSubsetPushforward_inverseImage_counit_isIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    IsIso ((closedSubsetStructureAdjunction (C := C) Z).counit) := by sorry
noncomputable def closedSubsetStructure_inverseImagePushforwardIso
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    closedSubsetPushforward (C := C) Z ⋙
        closedSubsetStructurePullback (C := C) Z ≅
      𝟭 (TopCat.Sheaf C (TopCat.of Z)) := by sorry
theorem closedSubsetPushforward_fullyFaithful
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z) :
    Nonempty (closedSubsetPushforward (C := C) Z).FullyFaithful := by sorry
theorem closedSubsetPushforward_mem_essImage_iff
    {C : Type u} [Category.{w} C]
    {FA : C → C → Type*} {CA : C → Type w}
    [∀ A B, FunLike (FA A B) (CA A) (CA B)]
    [ConcreteCategory.{w} C FA] [HasColimits C] [HasLimits C]
    [PreservesLimits (CategoryTheory.forget C)]
    [PreservesFilteredColimits (CategoryTheory.forget C)]
    [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (G : TopCat.Sheaf C X) :
    (closedSubsetPushforward (C := C) Z).essImage G ↔
      closedSubsetTerminalStalkCondition Z G := by sorry
def singletonSheaf (X : TopCat.{w}) : Sh.{w, w} X :=
  constantSheaf X (PUnit : Type w)

/-- The sheaf coproduct of two singleton sheaves is the source's two-point example. -/
abbrev twoPointSheaf (X : TopCat.{w}) : Sh.{w, w} X :=
  singletonSheaf X ⨿ singletonSheaf X

/-- Outside the closed subset, the two-point coproduct stalk is not the
    coproduct of the two singleton pushforward stalks. -/
theorem closedSubsetSetPushforward_stalk_twoPoint_mismatch
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ Nonempty
      ((((closedSubsetSetPushforward Z).obj (twoPointSheaf (TopCat.of Z))).presheaf.stalk x) ≃
        (((closedSubsetSetPushforward Z).obj (singletonSheaf (TopCat.of Z))).presheaf.stalk x) ⊕
          (((closedSubsetSetPushforward Z).obj (singletonSheaf (TopCat.of Z))).presheaf.stalk x)) := by sorry
theorem closedSubsetSetPushforward_not_rightExact
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ IsRightExact (closedSubsetSetPushforward Z) := by sorry
theorem closedSubsetSetPushforward_no_rightAdjoint
    {X : TopCat.{w}} {Z : Set X} (hZ : IsClosed Z)
    (x : X) (hx : x ∉ Z) :
    ¬ ∃ (R : Sh.{w, w} X ⥤ Sh.{w, w} (TopCat.of Z)),
      Nonempty (closedSubsetSetPushforward Z ⊣ R) := by sorry
