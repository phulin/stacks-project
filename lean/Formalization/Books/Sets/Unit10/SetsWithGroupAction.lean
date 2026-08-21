import Formalization.Books.Sets.Unit05.Hierarchy
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Set Theory, Chapter 10: Sets with group action

The canonical Mathlib model of a left `G`-set is `Action (Type u) G`.  The
textbook regards these objects as sets in the ambient cumulative hierarchy;
`GSetCoding` makes that set-theoretic representation explicit, as in the
coding bridge used in the preceding Sets chapter.  Since the type of all
`G`-sets is one universe above the underlying types, the ambient codes and
von Neumann levels live one universe above `GSet G`'s underlying universe;
this makes the full collection of codes a small family at the level where
ordinal bounds are formed.
-/

universe u v w

namespace Formalization.Books.Sets.Unit10

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ### The big category, size, and the bound -/

/-- The category of left `G`-sets, represented by Mathlib's action category. -/
abbrev GSet (G : Type u) [Group G] := Action (Type u) G

/-- The size of a `G`-set from the source section. -/
def gSetSize (G : Type u) [Group G] (S : GSet G) : Cardinal.{u} :=
  max Cardinal.aleph0 (max (Cardinal.mk G) (Cardinal.mk S.V))

/-- The bound used in this chapter: the countable power of a cardinal. -/
def Bound (κ : Cardinal.{u}) : Cardinal.{u} := κ ^ Cardinal.aleph0

/-! ### The ambient coding and `GSet α` -/

/-- A coding of the ambient category of `G`-sets by `ZFSet`s. -/
structure GSetCoding (G : Type u) [Group G] where
  code : GSet G → ZFSet.{u + 1}
  injective : Function.Injective code

/-- A coded `G`-set belongs to the von Neumann level `V_α`. -/
def GSetInLevel [Group G] (c : GSetCoding G) (α : Ordinal.{u + 1}) (S : GSet G) : Prop :=
  c.code S ∈ ZFSet.vonNeumann α

/-- The full subcategory of coded `G`-sets lying in `V_α`. -/
abbrev GSetLevel [Group G] (c : GSetCoding G) (α : Ordinal.{u + 1}) : Type _ :=
  ObjectProperty.FullSubcategory (GSetInLevel c α)

/-- The inclusion of `GSet α` into the big category of `G`-sets. -/
abbrev gSetInclusion [Group G] (c : GSetCoding G) (α : Ordinal.{u + 1}) :
    GSetLevel c α ⥤ GSet G :=
  ObjectProperty.ι (GSetInLevel c α)

/-- A `G`-set has a representative in `GSet α`. -/
def IsRepresentedAt [Group G] (c : GSetCoding G) (α : Ordinal.{u + 1}) (T : GSet G) : Prop :=
  ∃ S : GSetLevel c α, Nonempty (S.obj ≅ T)

/-! ### Countable limits and colimits -/

/-- The source's assertion that a limit in `GSet α` agrees with the ambient limit. -/
def GSetLimitConeAgreesWithAmbient [Group G] {c : GSetCoding G} {α : Ordinal.{u + 1}}
    {I : Type v} [Category.{w, v} I] (F : I ⥤ GSetLevel c α) : Prop :=
  ∀ (t : LimitCone F) (s : LimitCone (F ⋙ gSetInclusion c α)),
    Nonempty ((gSetInclusion c α).mapCone t.cone ≅ s.cone)

/-- The source's assertion that a colimit in `GSet α` agrees with the ambient colimit. -/
def GSetColimitCoconeAgreesWithAmbient [Group G] {c : GSetCoding G} {α : Ordinal.{u + 1}}
    {I : Type v} [Category.{w, v} I] (F : I ⥤ GSetLevel c α) : Prop :=
  ∀ (t : ColimitCocone F) (s : ColimitCocone (F ⋙ gSetInclusion c α)),
    Nonempty ((gSetInclusion c α).mapCocone t.cocone ≅ s.cocone)

/-- All closure and agreement properties asserted for a level in the first lemma. -/
structure GSetLevelData [Group G] (c : GSetCoding G) (S₀ : Set (GSet G))
    (α : Ordinal.{u + 1}) : Prop where
  isLimit : Order.IsSuccLimit α
  contains : S₀ ∪ {Action.leftRegular G} ⊆ {S | GSetInLevel c α S}
  bounded :
    ∀ S : GSetLevel c α, ∀ T : GSet G,
      gSetSize G T ≤ Bound (gSetSize G S.obj) → IsRepresentedAt c α T
  limits :
    ∀ {I : Type v} [Category.{w, v} I] [CountableCategory I]
      (F : I ⥤ GSetLevel c α),
      Nonempty (LimitCone (F ⋙ gSetInclusion c α)) ↔ Nonempty (LimitCone F)
  limit_agreement :
    ∀ {I : Type v} [Category.{w, v} I] [CountableCategory I]
      (F : I ⥤ GSetLevel c α), GSetLimitConeAgreesWithAmbient F
  colimits :
    ∀ {I : Type v} [Category.{w, v} I] [CountableCategory I]
      (F : I ⥤ GSetLevel c α),
      Nonempty (ColimitCocone (F ⋙ gSetInclusion c α)) ↔ Nonempty (ColimitCocone F)
  colimit_agreement :
    ∀ {I : Type v} [Category.{w, v} I] [CountableCategory I]
      (F : I ⥤ GSetLevel c α), GSetColimitCoconeAgreesWithAmbient F

/-! ### The first source lemma -/

/-- Lemma `lemma-sets-with-group-action` from the source. -/
theorem lemma_sets_with_group_action [Group G] (c : GSetCoding G) (S₀ : Set (GSet G)) :
    ∃ α : Ordinal.{u + 1}, GSetLevelData c S₀ α := by
  sorry

/-! ### Stable subsets -/

/-- The underlying map of the action of `g` on an object `U`. -/
def gSetMap [Group G] (U : GSet G) (g : G) (x : U.V) : U.V :=
  ConcreteCategory.hom (U.ρ g) x

/-- A subset of a `G`-set is stable under the action of `G`. -/
def IsGStableSubset [Group G] (U : GSet G) (O : Set U.V) : Prop :=
  ∀ (g : G) (x : U.V), x ∈ O → gSetMap U g x ∈ O

/-- The restricted `G`-set carried by a stable subset. -/
def restrictedGSet [Group G] {U : GSet G} {O : Set U.V} (hO : IsGStableSubset U O) : GSet G := by
  letI : MulAction G O := {
    smul g x := ⟨gSetMap U g x.1, hO g x.1 x.2⟩
    one_smul := by
      intro x
      apply Subtype.ext
      change gSetMap U 1 x.1 = x.1
      simp [gSetMap, Action.ρ_one]
    mul_smul := by
      intro g h x
      apply Subtype.ext
      change gSetMap U (g * h) x.1 = gSetMap U g (gSetMap U h x.1)
      change ConcreteCategory.hom (U.ρ (g * h)) x.1 =
        ConcreteCategory.hom (U.ρ g) (ConcreteCategory.hom (U.ρ h) x.1)
      rw [U.ρ.map_mul]
      rfl
  }
  exact Action.ofMulAction G O

/-! ### The second source lemma -/

/-- The regular `G`-set, finite (co)products, pullbacks, pushouts, and stable
subsets have the properties stated in `lemma-what-is-in-it-G-sets`. -/
theorem lemma_what_is_in_it_G_sets [Group G] {c : GSetCoding G} {S₀ : Set (GSet G)}
    {α : Ordinal.{u + 1}} (hα : GSetLevelData c S₀ α) :
    GSetInLevel c α (Action.leftRegular G) ∧
      HasFiniteProducts (GSetLevel c α) ∧
      HasFiniteCoproducts (GSetLevel c α) ∧
      HasPullbacks (GSetLevel c α) ∧
      HasPushouts (GSetLevel c α) ∧
      PreservesFiniteProducts (gSetInclusion c α) ∧
      PreservesFiniteCoproducts (gSetInclusion c α) ∧
      PreservesLimitsOfShape WalkingCospan (gSetInclusion c α) ∧
      PreservesColimitsOfShape WalkingSpan (gSetInclusion c α) ∧
      (∀ (U : GSetLevel c α) (O : Set U.obj.V) (hO : IsGStableSubset U.obj O),
        IsRepresentedAt c α (restrictedGSet hO)) := by
  sorry

end

end Formalization.Books.Sets.Unit10
