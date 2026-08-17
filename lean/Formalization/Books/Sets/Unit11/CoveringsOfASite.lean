import Formalization.Books.Sets.Unit07.Cofinality
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Set Theory, Chapter 11: Coverings of a site

The source section works with a category whose covering families may form a
proper class.  The indexed-family wrapper is retained where the source uses
the index set: it makes cardinal bounds and the source's combinatorial
equivalence literal while reusing Mathlib's `Over`, `Arrow`, pullback, and
presieve APIs.  The covering predicate itself is kept on indexed families,
since the source does not assume that combinatorially equivalent families are
literally the same covering.  A family has an index type in the arrow
universe, but the type of all such families is one universe higher; the
cardinal and von Neumann stages therefore use that higher universe so that an
arbitrary set of families has a genuine bound.

The source's `V_α` notation requires a coding of the category-theoretic data
as ZF sets.  `CoveringCoding` makes that ambient set-theoretic interface
explicit; `familyInV` and `arrowInV` then use Mathlib's actual von Neumann
hierarchy.  The coding level is one universe above the arrow level so that
the family type and arbitrary prescribed sets of families can be collected.
The reflection lemma itself is a statement interface and is left unproved at
this stage.
-/

universe u v w

namespace Formalization.Books.Sets.Unit11

open CategoryTheory CategoryTheory.Limits
open Set

noncomputable section

/-! ## Families with a fixed target -/

/-- An indexed family of arrows with target `X`.

The index type is chosen at the universe level at which all arrows of `C`
live.  This is the canonical size at which `Presieve.exists_eq_ofArrows`
represents an arbitrary presieve. -/
structure CoveringFamily (C : Type u) [Category.{v} C] (X : C) where
  Index : Type (max u v)
  arrow : Index → Over X

/-- A family without fixing its target in advance. -/
abbrev AnyCoveringFamily (C : Type u) [Category.{v} C] :=
  Σ X : C, CoveringFamily C X

namespace CoveringFamily

/-- Regard an indexed family as the corresponding Mathlib presieve. -/
def presieve {C : Type u} [Category.{v} C] {X : C} (F : CoveringFamily C X) :
    Presieve X :=
  Presieve.ofArrows (fun i => (F.arrow i).left) (fun i => (F.arrow i).hom)

@[simp]
theorem presieve_apply_arrow {C : Type u} [Category.{v} C] {X : C}
    (F : CoveringFamily C X) (i : F.Index) :
    F.presieve (F.arrow i).hom :=
  Presieve.ofArrows.mk i

/-- Package a fixed-target family as a family with an explicit target. -/
def asAny {C : Type u} [Category.{v} C] {X : C} (F : CoveringFamily C X) :
    AnyCoveringFamily C :=
  ⟨X, F⟩

/-- The singleton family used in the first site axiom. -/
def singleton {C : Type u} [Category.{v} C] {X Y : C} (f : Y ⟶ X) :
    CoveringFamily C X where
  Index := ULift.{max u v} (Fin 1)
  arrow := fun _ => Over.mk f

/-- Compose a covering family with a covering family over each member. -/
def bind {C : Type u} [Category.{v} C] {X : C} (U : CoveringFamily C X)
    (V : ∀ i, CoveringFamily C (U.arrow i).left) : CoveringFamily C X where
  Index := Σ i, (V i).Index
  arrow := fun ij =>
    Over.mk (((V ij.1).arrow ij.2).hom ≫ (U.arrow ij.1).hom)

/-- The chosen pullback family for a family and a map into its target. -/
def baseChange {C : Type u} [Category.{v} C] {X Y : C}
    (U : CoveringFamily C X) (f : Y ⟶ X)
    (h : ∀ i, HasPullback (U.arrow i).hom f) : CoveringFamily C Y where
  Index := U.Index
  arrow := fun i =>
    letI := h i
    Over.mk (pullback.snd (U.arrow i).hom f)

/-- The set of arrows occurring in a family. -/
def support {C : Type u} [Category.{v} C] {X : C} (F : CoveringFamily C X) :
    Set (Over X) :=
  Set.range F.arrow

/-- The source's combinatorial equivalence relation on families. -/
def combinatoriallyEquivalent {C : Type u} [Category.{v} C] {X : C}
    (U V : CoveringFamily C X) : Prop :=
  (∃ α : U.Index → V.Index, ∀ i, U.arrow i = V.arrow (α i)) ∧
    ∃ β : V.Index → U.Index, ∀ j, V.arrow j = U.arrow (β j)

/-- Combinatorial equivalence is exactly equality of the sets of arrows. -/
theorem combinatoriallyEquivalent_iff_support_eq {C : Type u} [Category.{v} C]
    {X : C} (U V : CoveringFamily C X) :
    combinatoriallyEquivalent U V ↔ U.support = V.support := by
  sorry

/-- The relation in the source is an equivalence relation. -/
instance setoid {C : Type u} [Category.{v} C] {X : C} :
    Setoid (CoveringFamily C X) where
  r := combinatoriallyEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro U
      exact ⟨⟨id, fun i => rfl⟩, id, fun i => rfl⟩
    · intro U V h
      rcases h with ⟨⟨α, hα⟩, β, hβ⟩
      exact ⟨⟨β, hβ⟩, α, hα⟩
    · intro U V W hUV hVW
      rcases hUV with ⟨⟨α, hα⟩, β, hβ⟩
      rcases hVW with ⟨⟨γ, hγ⟩, δ, hδ⟩
      exact ⟨⟨γ ∘ α, fun i => (hα i).trans (hγ (α i))⟩,
        β ∘ δ, fun j => (hδ j).trans (hβ (δ j))⟩

/-- Equivalent families induce the same presieve. -/
theorem presieve_eq_of_combinatoriallyEquivalent {C : Type u}
    [Category.{v} C] {X : C} {U V : CoveringFamily C X}
    (h : combinatoriallyEquivalent U V) : U.presieve = V.presieve := by
  sorry

end CoveringFamily

/-! ## The covering predicate and the three site axioms -/

/-- A covering class on `C` satisfying the three axioms used in the source.

Unlike `CategoryTheory.Pretopology`, this interface does not require global
pullbacks: the third field asks for pullbacks only along a covering family,
which is exactly the hypothesis in the book. -/
structure SiteCoveringClass (C : Type u) [Category.{v} C] where
  covering : ∀ X : C, CoveringFamily C X → Prop
  has_isos : ∀ {X Y : C} (f : Y ⟶ X) [IsIso f],
    covering X (CoveringFamily.singleton f)
  transitive : ∀ {X : C} (U : CoveringFamily C X),
    covering X U →
      ∀ (V : ∀ i, CoveringFamily C (U.arrow i).left),
        (∀ i, covering (U.arrow i).left (V i)) →
          covering X (CoveringFamily.bind U V)
  base_change : ∀ {X Y : C} (U : CoveringFamily C X),
    covering X U →
      ∀ (f : Y ⟶ X),
        ∃ h : ∀ i, HasPullback (U.arrow i).hom f,
          covering Y (CoveringFamily.baseChange U f h)

namespace SiteCoveringClass

/-- A family is covering according to the indexed-family predicate. -/
def isCovering {C : Type u} [Category.{v} C] (K : SiteCoveringClass C)
    {X : C} (F : CoveringFamily C X) : Prop :=
  K.covering X F

/-- The class of all covering families of `K`. -/
def allCoverings {C : Type u} [Category.{v} C] (K : SiteCoveringClass C) :
    Set (AnyCoveringFamily C) :=
  {F | K.isCovering F.2}

end SiteCoveringClass

/-- A set of families satisfies the three site axioms. -/
def IsSiteCoveringCollection {C : Type u} [Category.{v} C]
    (S : Set (AnyCoveringFamily C)) : Prop :=
  (∀ {X Y : C} (f : Y ⟶ X) [IsIso f],
      (CoveringFamily.singleton f).asAny ∈ S) ∧
    (∀ {X : C} (U : CoveringFamily C X),
      U.asAny ∈ S →
        ∀ (V : ∀ i, CoveringFamily C (U.arrow i).left),
          (∀ i, (V i).asAny ∈ S) →
            (CoveringFamily.bind U V).asAny ∈ S) ∧
    (∀ {X Y : C} (U : CoveringFamily C X), U.asAny ∈ S →
      ∀ (f : Y ⟶ X),
        ∃ h : ∀ i, HasPullback (U.arrow i).hom f,
          (CoveringFamily.baseChange U f h).asAny ∈ S)

/-! ## Von Neumann levels and cardinal-restricted coverings -/

/-- A coding of arrows and covering families by ZF sets.

This is the explicit ambient-set interface behind the source's use of
  `V_α`.  The injectivity fields prevent the coding from identifying distinct
  category-theoretic data, and the singleton field records the set-theoretic
  closure needed for the first site axiom at a bounded stage.  The codes live
  one universe above the arrows because `AnyCoveringFamily C` itself contains
  an index type and lives one universe above its index. -/
structure CoveringCoding (C : Type u) [Category.{v} C] where
  familyCode : AnyCoveringFamily C → ZFSet.{max (u + 1) (v + 1)}
  familyCode_injective : Function.Injective familyCode
  arrowCode : Arrow C → ZFSet.{max (u + 1) (v + 1)}
  arrowCode_injective : Function.Injective arrowCode
  /-- Singleton families are one hierarchy step above their arrows. -/
  singleton_family_mem_of_arrow_mem :
    ∀ {X Y : C} (f : Y ⟶ X) (α : Ordinal.{max (u + 1) (v + 1)}),
      arrowCode (Arrow.mk f) ∈ ZFSet.vonNeumann α →
        familyCode (CoveringFamily.singleton f).asAny ∈
          ZFSet.vonNeumann (α + 1)

namespace CoveringCoding

/-- Membership of a family in the von Neumann level `V_α`. -/
def familyInV {C : Type u} [Category.{v} C] (H : CoveringCoding C)
    (F : AnyCoveringFamily C) (α : Ordinal.{max (u + 1) (v + 1)}) : Prop :=
  H.familyCode F ∈ ZFSet.vonNeumann α

/-- Membership of an arrow in the von Neumann level `V_α`. -/
def arrowInV {C : Type u} [Category.{v} C] (H : CoveringCoding C)
    (f : Arrow C) (α : Ordinal.{max (u + 1) (v + 1)}) : Prop :=
  H.arrowCode f ∈ ZFSet.vonNeumann α

end CoveringCoding

namespace SiteCoveringClass

/-- The coverings below `α`, corresponding to `Cov(C)_α`. -/
def coveringsAt {C : Type u} [Category.{v} C] (K : SiteCoveringClass C)
    (H : CoveringCoding C) (α : Ordinal.{max (u + 1) (v + 1)}) :
    Set (AnyCoveringFamily C) :=
  {F | F ∈ allCoverings K ∧ H.familyInV F α}

/-- The coverings below `α` whose index has cardinal at most `κ`. -/
def coveringsAtCardinal {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α : Ordinal.{max (u + 1) (v + 1)}) :
    Set (AnyCoveringFamily C) :=
  {F | F ∈ coveringsAt K H α ∧
    Cardinal.lift.{max (u + 1) (v + 1), max u v}
      (Cardinal.mk F.2.Index) ≤ κ}

end SiteCoveringClass

/-! ## Supports and the first bounding ordinal -/

/-- A set of arrows with a fixed target. -/
abbrev TargetedSupport (C : Type u) [Category.{v} C] :=
  Σ X : C, Set (Over X)

/-- The set `𝒮` of all sets of arrows with a fixed target. -/
def allTargetedSupports {C : Type u} [Category.{v} C] :
    Set (TargetedSupport C) :=
  Set.univ

/-- The support of a family packaged with its target. -/
def packagedSupport {C : Type u} [Category.{v} C]
    (F : AnyCoveringFamily C) : TargetedSupport C :=
  ⟨F.1, F.2.support⟩

/-- The subset `𝒮_τ` of supports of covering families. -/
def coveringSupports {C : Type u} [Category.{v} C] (K : SiteCoveringClass C) :
    Set (TargetedSupport C) :=
  {T | ∃ F : CoveringFamily C T.1,
      K.isCovering F ∧ F.support = T.2}

/-- The least stage at which a support of a covering occurs. -/
noncomputable def leastCoveringStage {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C) (T : TargetedSupport C) :
    Ordinal.{max (u + 1) (v + 1)} :=
  sInf {β | ∃ F : CoveringFamily C T.1,
    K.isCovering F ∧ F.support = T.2 ∧
      F.asAny ∈ K.coveringsAt H β}

/-- The source's first global bounding ordinal `β₀`. -/
noncomputable def initialCoveringStage {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C) :
    Ordinal.{max (u + 1) (v + 1)} :=
  sSup (leastCoveringStage K H '' coveringSupports K)

theorem leastCoveringStage_isLeast {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C) (T : TargetedSupport C)
    (hT : T ∈ coveringSupports K) :
    IsLeast {β | ∃ F : CoveringFamily C T.1,
      K.isCovering F ∧ F.support = T.2 ∧
        F.asAny ∈ K.coveringsAt H β}
      (leastCoveringStage K H T) := by
  sorry

/-- Every covering has an equivalent representative below `β₀`. -/
theorem exists_combinatoriallyEquivalent_mem_coveringsAt_initialStage
    {C : Type u} [Category.{v} C] (K : SiteCoveringClass C)
    (H : CoveringCoding C) {X : C} (U : CoveringFamily C X)
    (hU : K.isCovering U) :
    ∃ V : CoveringFamily C X,
      K.isCovering V ∧
        V.asAny ∈ K.coveringsAt H (initialCoveringStage K H) ∧
        CoveringFamily.combinatoriallyEquivalent U V := by
  sorry

/-! ## The cardinal bound `κ` -/

/-- The cardinality of a family index. -/
def indexCardinal {C : Type u} [Category.{v} C] {X : C}
    (F : CoveringFamily C X) : Cardinal.{max (u + 1) (v + 1)} :=
  Cardinal.lift.{max (u + 1) (v + 1), max u v} (Cardinal.mk F.Index)

/-- The supremum of the index cardinalities of a set of families. -/
noncomputable def supIndexCardinal {C : Type u} [Category.{v} C]
    (S : Set (AnyCoveringFamily C)) : Cardinal.{max (u + 1) (v + 1)} :=
  sSup ((fun F => indexCardinal F.2) '' S)

/-- The cardinality of the category's collection of arrows. -/
def arrowCardinal {C : Type u} [Category.{v} C] : Cardinal.{max (u + 1) (v + 1)} :=
  Cardinal.lift.{max (u + 1) (v + 1), max u v} (Cardinal.mk (Arrow C))

/-- The source's maximum of `aleph₀`, all arrows, and the relevant index bounds. -/
noncomputable def initialCardinalBound {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (Cov₀ : Set (AnyCoveringFamily C)) :
    Cardinal.{max (u + 1) (v + 1)} :=
  max (Cardinal.aleph0 : Cardinal.{max (u + 1) (v + 1)})
    (max (arrowCardinal (C := C))
      (max (supIndexCardinal (K.coveringsAt H (initialCoveringStage K H)))
        (supIndexCardinal Cov₀)))

theorem aleph0_le_initialCardinalBound {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (Cov₀ : Set (AnyCoveringFamily C)) :
    Cardinal.aleph0 ≤ initialCardinalBound K H Cov₀ := by
  exact le_max_left _ _

theorem initialCardinalBound_mul_self {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (Cov₀ : Set (AnyCoveringFamily C)) :
    initialCardinalBound K H Cov₀ * initialCardinalBound K H Cov₀ =
      initialCardinalBound K H Cov₀ := by
  exact Cardinal.mul_eq_self (aleph0_le_initialCardinalBound K H Cov₀)

/-- At `β₀`, the cardinal restriction is redundant by construction of `κ`. -/
theorem coveringsAt_initialStage_eq_cardinal_restriction
    {C : Type u} [Category.{v} C] (K : SiteCoveringClass C)
    (H : CoveringCoding C) (Cov₀ : Set (AnyCoveringFamily C)) :
    K.coveringsAt H (initialCoveringStage K H) =
      K.coveringsAtCardinal H (initialCardinalBound K H Cov₀)
        (initialCoveringStage K H) := by
  sorry

/-! ## The transfinite closure function -/

/-- The ordinal condition defining the successor step of the source's `f`.

The successor condition is strict at the previous closure stage so that
values at a limit input remain cofinal below the limit value.  The source's
displayed base-change clause is indexed by `α`, but its later closure-stage
argument needs the coverings at `f(α)`; this interface uses `fα` for that
corrected clause. -/
def successorClosureCondition {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α fα β : Ordinal.{max (u + 1) (v + 1)}) : Prop :=
  α + 1 ≤ β ∧ fα < β ∧
    (∀ {X : C} (U : CoveringFamily C X),
      U.asAny ∈ K.coveringsAtCardinal H κ fα →
        ∀ (V : ∀ i, CoveringFamily C (U.arrow i).left),
          (∀ i, (V i).asAny ∈ K.coveringsAtCardinal H κ fα) →
            (CoveringFamily.bind U V).asAny ∈
              K.coveringsAtCardinal H κ β) ∧
    (∀ {X Y : C} (U : CoveringFamily C X),
      U.asAny ∈ K.coveringsAtCardinal H κ fα →
        ∀ (f : Y ⟶ X),
          ∃ h : ∀ i, HasPullback (U.arrow i).hom f,
            (CoveringFamily.baseChange U f h).asAny ∈
              K.coveringsAtCardinal H κ β)

/-- The collection whose least element is `f(α + 1)`. -/
def successorClosureOrdinals {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α fα : Ordinal.{max (u + 1) (v + 1)}) :
    Set (Ordinal.{max (u + 1) (v + 1)}) :=
  {β | successorClosureCondition K H κ α fα β}

/-- The source's least successor-stage ordinal (used under an infinite
    cardinal bound). -/
noncomputable def successorClosureStage {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α fα : Ordinal.{max (u + 1) (v + 1)}) :
    Ordinal.{max (u + 1) (v + 1)} :=
  sInf (successorClosureOrdinals K H κ α fα)

theorem successorClosureOrdinals_nonempty {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (hκ : Cardinal.aleph0 ≤ κ)
    (α fα : Ordinal.{max (u + 1) (v + 1)}) :
    (successorClosureOrdinals K H κ α fα).Nonempty := by
  sorry

/-! The infinite-cardinal witness is required because the composition of two
    `κ`-bounded families is `κ`-bounded only in that range. -/
theorem successorClosureStage_isLeast {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (hκ : Cardinal.aleph0 ≤ κ)
    (α fα : Ordinal.{max (u + 1) (v + 1)}) :
    IsLeast (successorClosureOrdinals K H κ α fα)
      (successorClosureStage K H κ α fα) := by
  sorry

/-- The function `f` defined by transfinite induction in the source. -/
noncomputable def closureFunction {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α : Ordinal.{max (u + 1) (v + 1)}) :
    Ordinal.{max (u + 1) (v + 1)} :=
  Ordinal.limitRecOn
    (motive := fun _ : Ordinal.{max (u + 1) (v + 1)} =>
      Ordinal.{max (u + 1) (v + 1)})
    α 0
    (fun α fα => successorClosureStage K H κ α fα)
    (fun α _ ih => ⨆ a : Set.Iio α, ih a.1 a.2)

theorem closureFunction_zero {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)}) :
    closureFunction K H κ 0 = 0 := by
  sorry

theorem closureFunction_add_one {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (α : Ordinal.{max (u + 1) (v + 1)}) :
    closureFunction K H κ (α + 1) =
      successorClosureStage K H κ α (closureFunction K H κ α) := by
  sorry

theorem closureFunction_limit {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    {α : Ordinal.{max (u + 1) (v + 1)}}
    (hα : Order.IsSuccLimit α) :
    closureFunction K H κ α =
      ⨆ a : Set.Iio α, closureFunction K H κ a.1 := by
  sorry

theorem closureFunction_monotone {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (hκ : Cardinal.aleph0 ≤ κ) :
    Monotone (closureFunction K H κ) := by
  sorry

theorem le_closureFunction {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (hκ : Cardinal.aleph0 ≤ κ)
    (α : Ordinal.{max (u + 1) (v + 1)}) :
    α ≤ closureFunction K H κ α := by
  sorry

theorem closureFunction_preserves_stage_bounds {C : Type u}
    [Category.{v} C] (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (hκ : Cardinal.aleph0 ≤ κ)
    (Cov₀ : Set (AnyCoveringFamily C))
    {β₁ β : Ordinal.{max (u + 1) (v + 1)}} (hβ₁ : β₁ ≤ β)
    (hArrows : ∀ a : Arrow C, H.arrowInV a β₁)
    (hCov₀ : ∀ F ∈ Cov₀, H.familyInV F β₁) :
    (∀ a : Arrow C, H.arrowInV a (closureFunction K H κ β)) ∧
      ∀ F ∈ Cov₀, H.familyInV F (closureFunction K H κ β) := by
  sorry

/-! ## The final cofinal stage and the bounded site -/

theorem exists_first_large_stage {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (Cov₀ : Set (AnyCoveringFamily C)) :
    ∃ β₁ : Ordinal.{max (u + 1) (v + 1)},
      initialCoveringStage K H ≤ β₁ ∧
        (∀ a : Arrow C, H.arrowInV a β₁) ∧
        (∀ F ∈ Cov₀, H.familyInV F β₁) := by
  sorry

theorem exists_second_stage
    (κ : Cardinal.{w}) (β₁ : Ordinal.{w}) :
    ∃ β₂ : Ordinal.{w}, β₁ < β₂ ∧ κ < Ordinal.cof β₂ := by
  sorry

theorem second_stage_is_limit
    (κ : Cardinal.{w}) (β₂ : Ordinal.{w})
    (hκ : Cardinal.aleph0 ≤ κ) (hcf : κ < Ordinal.cof β₂) :
    Order.IsSuccLimit β₂ := by
  sorry

theorem closureFunction_values_cofinal {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    {β₂ : Ordinal.{max (u + 1) (v + 1)}}
    (hβ₂ : Order.IsSuccLimit β₂) :
    ∀ γ < closureFunction K H κ β₂,
      ∃ β : Set.Iio β₂, γ < closureFunction K H κ β.1 := by
  sorry

theorem exists_common_closure_stage {C : Type u} [Category.{v} C]
    {β₂ : Ordinal.{max (u + 1) (v + 1)}}
    (hβ₂ : Order.IsSuccLimit β₂)
    {I : Type (max u v)}
    (hI : Cardinal.lift.{max (u + 1) (v + 1), max u v}
      (Cardinal.mk I) < Ordinal.cof β₂)
    (b : I → Ordinal.{max (u + 1) (v + 1)})
    (hb : ∀ i, b i < β₂) :
    ∃ β : Set.Iio β₂, ∀ i, b i < β.1 := by
  sorry

theorem vonNeumann_mem_closureFunction_iff {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    {β₂ : Ordinal.{max (u + 1) (v + 1)}}
    (hβ₂ : Order.IsSuccLimit β₂)
    (x : ZFSet.{max (u + 1) (v + 1)}) :
    x ∈ ZFSet.vonNeumann (closureFunction K H κ β₂) ↔
      ∃ β : Set.Iio β₂,
        x ∈ ZFSet.vonNeumann (closureFunction K H κ β.1) := by
  sorry

/-- The least `β` with `U ∈ Cov_{κ,f(β)}`. -/
noncomputable def firstClosureIndex {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    (β₂ : Ordinal.{max (u + 1) (v + 1)})
    (F : AnyCoveringFamily C) :
    Ordinal.{max (u + 1) (v + 1)} :=
  sInf {β | β < β₂ ∧ F ∈ K.coveringsAtCardinal H κ
      (closureFunction K H κ β)}

theorem firstClosureIndex_lt_second {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    {β₂ : Ordinal.{max (u + 1) (v + 1)}}
    (hβ₂ : Order.IsSuccLimit β₂) {F : AnyCoveringFamily C}
    (hF : F ∈ K.coveringsAtCardinal H κ
      (closureFunction K H κ β₂)) :
    firstClosureIndex K H κ β₂ F < β₂ := by
  sorry

theorem boundedCoverings_at_closureStage_isSite {C : Type u}
    [Category.{v} C] (K : SiteCoveringClass C)
    (H : CoveringCoding C)
    (κ : Cardinal.{max (u + 1) (v + 1)})
    {β₁ β₂ : Ordinal.{max (u + 1) (v + 1)}}
    (hArrows : ∀ a : Arrow C, H.arrowInV a β₁)
    (hκ : Cardinal.aleph0 ≤ κ)
    (hβ₂ : β₁ < β₂ ∧ κ < Ordinal.cof β₂) :
    Order.IsSuccLimit (closureFunction K H κ β₂) ∧
      IsSiteCoveringCollection
        (K.coveringsAtCardinal H κ (closureFunction K H κ β₂)) := by
  sorry

/-! ## The reflection lemma -/

/--
The set-sized replacement for a proper-class collection of coverings.

This is the source lemma `lemma-coverings-site`: the chosen cardinal and
limit ordinal contain the prescribed set, their bounded coverings satisfy all
three site axioms, and every original covering has a combinatorially
equivalent bounded representative.
-/
theorem covering_reflection
    {C : Type u} [Category.{v} C] (K : SiteCoveringClass C)
    (H : CoveringCoding C) (Cov₀ : Set (AnyCoveringFamily C))
    (hCov₀ : Cov₀ ⊆ K.allCoverings) :
    ∃ κ : Cardinal.{max (u + 1) (v + 1)},
      ∃ α : Ordinal.{max (u + 1) (v + 1)},
      Order.IsSuccLimit α ∧
        Cov₀ ⊆ K.coveringsAtCardinal H κ α ∧
          IsSiteCoveringCollection (K.coveringsAtCardinal H κ α) ∧
            ∀ F ∈ K.allCoverings,
              ∃ G : CoveringFamily C F.1,
                G.asAny ∈ K.coveringsAtCardinal H κ α ∧
                  CoveringFamily.combinatoriallyEquivalent F.2 G := by
  sorry

/-! ## The final warning in the source -/

/-- Candidate statement corresponding to the source's final warning.

The source says it is likely that a limit level already works, but does not
assert this.  This definition records the proposed property without turning
the warning into an unproved theorem. -/
def limitLevelAlreadyWorks {C : Type u} [Category.{v} C]
    (K : SiteCoveringClass C) (H : CoveringCoding C) : Prop :=
  ∃ α : Ordinal.{max (u + 1) (v + 1)},
    Order.IsSuccLimit α ∧
      IsSiteCoveringCollection (K.coveringsAt H α) ∧
        ∀ F ∈ K.allCoverings,
          ∃ G : CoveringFamily C F.1,
            G.asAny ∈ K.coveringsAt H α ∧
              CoveringFamily.combinatoriallyEquivalent F.2 G

end

end Formalization.Books.Sets.Unit11
