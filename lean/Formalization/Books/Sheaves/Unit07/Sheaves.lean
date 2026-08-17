import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Mathlib.Data.Int.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Sheaves on Spaces, Chapter 7: Sheaves

The source section is formalized with Mathlib's canonical sheaf condition and
the canonical sheaves of functions.  The direct-sum example reuses the
presheaf constructed in Chapter 4 rather than introducing a second version
of that presheaf.
-/

namespace Formalization.Books.Sheaves.Unit07

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Formalization.Books.Sheaves.Unit03
open Formalization.Books.Sheaves.Unit04
open scoped DirectSum

universe w v u

/-! ## The sheaf condition and the category of sheaves -/

/-- A set-valued presheaf satisfying the canonical sheaf condition. -/
abbrev SetSheaf {X : TopCat.{v}} (F : Presheaf.{w, v} X) : Prop :=
  TopCat.Presheaf.IsSheaf F

/-- The category `Sh(X)` of sheaves of sets on `X`. -/
abbrev Sh (X : TopCat.{v}) := TopCat.Sheaf (Type w) X

/-- A morphism in `Sh(X)`, whose underlying map is a presheaf morphism. -/
abbrev SetSheafMorphism {X : TopCat.{v}} (F G : Sh.{w, v} X) := F ⟶ G

/-- Compatibility of a family of sections on an open cover. -/
abbrev CompatibleSections {X : TopCat.{v}} {F : Presheaf.{w, v} X}
    {ι : Type v} (U : ι → Opens X) (s : ∀ i, Sections F (U i)) : Prop :=
  TopCat.Presheaf.IsCompatible F U s

/-- The assertion that a section glues a compatible family on an open cover. -/
abbrev IsGluingSections {X : TopCat.{v}} {F : Presheaf.{w, v} X}
    {ι : Type v} (U : ι → Opens X) (s : ∀ i, Sections F (U i))
    (t : Sections F (iSup U)) : Prop :=
  TopCat.Presheaf.IsGluing F U s t

/-- The source's elementwise sheaf condition, via Mathlib's unique-gluing API. -/
theorem setSheaf_iff_unique_gluing {X : TopCat.{v}} (F : Presheaf.{w, v} X) :
    SetSheaf F ↔
      ∀ ⦃ι : Type v⦄ (U : ι → Opens X) (s : ∀ i, Sections F (U i)),
        CompatibleSections U s →
          ∃! t : Sections F (iSup U), IsGluingSections U s t := by
  change TopCat.Presheaf.IsSheaf F ↔
    TopCat.Presheaf.IsSheafUniqueGluing F
  exact TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types F

/-! ## Empty covers and disjoint unions -/

/-- The empty-cover case makes the sections on the empty open terminal. -/
noncomputable def setSheaf_sections_empty_isTerminal {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    IsTerminal (F.obj (op (⊥ : Opens X))) := by
  exact TopCat.Sheaf.isTerminalOfEmpty (⟨F, hF⟩ : TopCat.Sheaf (Type w) X)

/-- In `Type`, the terminal sections on the empty open form a singleton type. -/
theorem setSheaf_sections_empty_unique {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    Nonempty (Sections F (⊥ : Opens X)) ∧
      Subsingleton (Sections F (⊥ : Opens X)) := by
  let hUnique : Unique (Sections F (⊥ : Opens X)) :=
    (Types.isTerminalEquivUnique _).toFun (setSheaf_sections_empty_isTerminal hF)
  exact ⟨⟨hUnique.default⟩, ⟨fun a b => (hUnique.uniq a).trans (hUnique.uniq b).symm⟩⟩

/-- Sections over disjoint opens are the product of the two section types. -/
theorem setSheaf_disjoint_union_sections_equiv {X : TopCat.{v}}
    {F : Presheaf.{w, v} X} (hF : SetSheaf F) {U V : Opens X}
    (hUV : Disjoint U V) :
    Nonempty (Sections F (U ⊔ V) ≃ Sections F U × Sections F V) := by
  sorry

/-! ## Continuous functions and constant sheaves -/

/-- The presheaf of continuous functions from opens of `X` to `Y`. -/
def continuousFunctionsPresheaf (X Y : TopCat.{u}) :
    TopCat.Presheaf (Type u) X :=
  TopCat.presheafToTop X Y

/-- Sections of the continuous-functions presheaf are continuous maps on an open. -/
@[simp]
theorem continuousFunctionsPresheaf_obj (X Y : TopCat.{u}) (U : Opens X) :
    (continuousFunctionsPresheaf X Y).obj (op U) =
      ((Opens.toTopCat X).obj U ⟶ Y) := rfl

/-- The restriction operation in the continuous-functions presheaf. -/
abbrev continuousFunctionsRestriction (X Y : TopCat.{u}) {U V : Opens X}
    (i : V ⟶ U) (f : ToType ((continuousFunctionsPresheaf X Y).obj (op U))) :
    ToType ((continuousFunctionsPresheaf X Y).obj (op V)) :=
  TopCat.Presheaf.restrict f i

/-- The sheaf of continuous functions from opens of `X` to `Y`. -/
def continuousFunctionsSheaf (X Y : TopCat.{u}) :
    TopCat.Sheaf (Type u) X :=
  TopCat.sheafToTop (X := X) Y

/-- Continuous functions glue to a continuous function on an open cover. -/
theorem continuousFunctionsPresheaf_isSheaf (X Y : TopCat.{u}) :
    SetSheaf (continuousFunctionsPresheaf X Y) := by
  exact (continuousFunctionsSheaf X Y).property

/-- For a discrete target, continuity is equivalent to local constancy. -/
theorem continuous_iff_locallyConstant_of_discrete
    {Z A : Type u} [TopologicalSpace Z] [TopologicalSpace A]
    [DiscreteTopology A] (f : Z → A) :
    Continuous f ↔ IsLocallyConstant f := by
  exact (IsLocallyConstant.iff_continuous f).symm

/-- The set of locally constant sections on an open, as used in the source. -/
abbrev LocallyConstantSections (X : TopCat.{u}) (A : Type u) (U : Opens X) :=
  {f : U → A // IsLocallyConstant f}

/-- The constant sheaf with value `A`, using the discrete topology on `A`. -/
def constantSheaf (X : TopCat.{u}) (A : Type u) :
    TopCat.Sheaf (Type u) X :=
  continuousFunctionsSheaf X (TopCat.discrete.obj A)

/-- The underlying presheaf of the constant sheaf is the continuous-functions presheaf. -/
@[simp]
theorem constantSheaf_presheaf (X : TopCat.{u}) (A : Type u) :
    (constantSheaf X A).presheaf =
      continuousFunctionsPresheaf X (TopCat.discrete.obj A) := rfl

/-- The sections of the constant sheaf are the locally constant maps. -/
theorem constantSheaf_sections_equiv (X : TopCat.{u}) (A : Type u) (U : Opens X) :
    Nonempty (Sections (constantSheaf X A).presheaf U ≃
      LocallyConstantSections X A U) := by
  sorry

/-! ## Pointwise products of stalkwise sets -/

/-- The presheaf whose sections over `U` are dependent products of the `A x`. -/
def pointwiseProductPresheaf {X : TopCat.{v}} (A : X → Type w) :
    TopCat.Presheaf (Type (max v w)) X :=
  TopCat.presheafToTypes X A

/-- Sections of the pointwise product presheaf are dependent functions on the open. -/
@[simp]
theorem pointwiseProductPresheaf_obj {X : TopCat.{v}} (A : X → Type w)
    (U : Opens X) :
    (pointwiseProductPresheaf A).obj (op U) = ∀ x : U, A x := rfl

/-- Restriction in the pointwise product presheaf is pointwise restriction. -/
theorem pointwiseProductPresheaf_restriction {X : TopCat.{v}} (A : X → Type w)
    {U V : Opens X} (i : V ⟶ U) (s : ∀ x : U, A x) :
    TopCat.Presheaf.restrict (F := pointwiseProductPresheaf A) s i =
      fun x : V => s (i x) := rfl

/-- The pointwise product presheaf is a sheaf. -/
theorem pointwiseProductPresheaf_isSheaf {X : TopCat.{v}} (A : X → Type w) :
    SetSheaf (pointwiseProductPresheaf A) :=
  TopCat.Presheaf.toTypes_isSheaf X A

/-- The corresponding pointwise product sheaf. -/
def pointwiseProductSheaf {X : TopCat.{v}} (A : X → Type w) :
    TopCat.Sheaf (Type (max v w)) X :=
  ⟨pointwiseProductPresheaf A, pointwiseProductPresheaf_isSheaf A⟩

/-! ## Direct sums over points -/

/-- The set-valued form of Unit04's direct-sum-over-points presheaf. -/
noncomputable abbrev directSumPresheafOfSets {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] :
    TopCat.Presheaf (Type (max v w)) X :=
  Formalization.Books.Sheaves.Unit04.underlyingPresheaf
    (Formalization.Books.Sheaves.Unit04.directSumPresheaf M)

/-- Sections of the direct-sum presheaf are direct sums over the open. -/
@[simp]
theorem directSumPresheafOfSets_sections {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] (U : Opens X) :
    Sections (directSumPresheafOfSets M) U = (⨁ x : U, M x) := rfl

/-- Restriction in the direct-sum presheaf discards summands outside the smaller open. -/
theorem directSumPresheafOfSets_restriction {X : TopCat.{v}} (M : X → Type w)
    [∀ x, AddCommGroup (M x)] {U V : Opens X} (h : V ≤ U)
    (s : Sections (directSumPresheafOfSets M) U) :
    TopCat.Presheaf.restrict (F := directSumPresheafOfSets M) s (homOfLE h) =
      Formalization.Books.Sheaves.Unit04.directSumRestriction M h s := rfl

/-- A singleton open in a discrete space. -/
def singletonOpen (X : TopCat.{v}) [DiscreteTopology X] (x : X) : Opens X :=
  ⟨{x}, isOpen_discrete _⟩

/-- On a discrete space, the sheaf condition identifies sections with singleton data. -/
theorem setSheaf_sections_top_equiv_singletons {X : TopCat.{v}}
    [DiscreteTopology X] {F : Presheaf.{w, v} X} (hF : SetSheaf F) :
    Nonempty (Sections F (⊤ : Opens X) ≃
      ∀ x : X, Sections F (singletonOpen X x)) := by
  sorry

/-- For the direct-sum presheaf, the discrete infinite sheaf condition would
force a direct-sum/product additive equivalence. -/
theorem directSumPresheaf_sheaf_implies_sum_product {X : TopCat.{v}}
    (hX : Infinite X) [DiscreteTopology X] (M : X → Type w)
    [∀ x, AddCommGroup (M x)]
    (hF : SetSheaf (directSumPresheafOfSets M)) :
    Nonempty ((⨁ x : X, M x) ≃+ (∀ x : X, M x)) := by
  sorry

/-- A genuine direct-sum/product mismatch prevents the direct-sum presheaf
from being a sheaf on an infinite discrete space. -/
theorem directSumPresheaf_not_sheaf_of_sum_product_gap {X : TopCat.{v}}
    (hX : Infinite X) [DiscreteTopology X] (M : X → Type w)
    [∀ x, AddCommGroup (M x)]
    (hgap : ¬ Nonempty ((⨁ x : X, M x) ≃+ (∀ x : X, M x))) :
    ¬ SetSheaf (directSumPresheafOfSets M) := by
  intro hF
  exact hgap (directSumPresheaf_sheaf_implies_sum_product hX M hF)

/-- The standard countable family of integer groups exhibits the
direct-sum/product mismatch mentioned in the source. -/
theorem directSum_product_gap_nat :
    ¬ Nonempty ((⨁ _ : ℕ, ℤ) ≃+ (ℕ → ℤ)) := by
  sorry

/-- The direct-sum presheaf is not a sheaf for the standard infinite discrete
space and integer-valued family. -/
theorem directSumPresheaf_not_sheaf_nat :
    ¬ SetSheaf
      (directSumPresheafOfSets (X := TopCat.discrete.obj ℕ)
        (fun _ : ℕ => ℤ)) := by
  apply directSumPresheaf_not_sheaf_of_sum_product_gap
    (inferInstanceAs (Infinite ℕ))
  exact directSum_product_gap_nat

/-- If every open is quasi-compact, the direct-sum-over-points presheaf is a sheaf. -/
theorem directSumPresheaf_isSheaf_of_compact_opens {X : TopCat.{v}}
    (M : X → Type w) [∀ x, AddCommGroup (M x)]
    (hcompact : ∀ U : Opens X, IsCompact (U : Set X)) :
    SetSheaf (directSumPresheafOfSets M) := by
  sorry

end Formalization.Books.Sheaves.Unit07
