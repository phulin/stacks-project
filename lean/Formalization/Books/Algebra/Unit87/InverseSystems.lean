import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.PNat.Basic

/-!
# Commutative Algebra, Chapter 87: Inverse systems

The source indexes inverse systems by the positive natural numbers.  The
canonical `InverseSystem` functor from the preceding chapters records all
transition maps and their identity and composition laws; the declarations
below expose the successive maps and the compatible-family description used
in this chapter.
-/

namespace Formalization.Books.Algebra.Unit87

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit21

universe u w

noncomputable section

/-! ## Inverse systems over the positive integers -/

/- The source's sequence of modules and its converse description by all
transition maps are already exactly `InverseSystem ℕ+ (ModuleCat R)`. -/
abbrev NaturalInverseSystem (R : Type u) [Ring R] :=
  InverseSystem ℕ+ (ModuleCat.{w} R)

/- The map from stage `i` to stage `j` for `j ≤ i` is the image of the unique
morphism `op i ⟶ op j` in the opposite preorder category. -/
def transitionMap {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) {i j : ℕ+} (h : j ≤ i) :
    F.obj (Opposite.op i) ⟶ F.obj (Opposite.op j) :=
  F.map (opHomOfLE h)

@[simp] theorem transitionMap_refl {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) (i : ℕ+) :
    transitionMap F (i := i) (j := i) le_rfl = 𝟙 (F.obj (Opposite.op i)) := by
  simp [transitionMap, opHomOfLE]

/- Functoriality is the source's displayed identity
`φ_{ii''} = φ_{i'i''} ∘ φ_{ii'}`. -/
theorem transitionMap_comp {R : Type u} [Ring R]
    (F : NaturalInverseSystem R)
    {i j k : ℕ+} (hij : j ≤ i) (hjk : k ≤ j) :
    transitionMap F (i := i) (j := j) hij ≫
        transitionMap F (i := j) (j := k) hjk =
      transitionMap F (i := i) (j := k) (hjk.trans hij) := by
  change F.map (homOfLE hij).op ≫ F.map (homOfLE hjk).op =
    F.map (homOfLE (hjk.trans hij)).op
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/- The displayed arrow `φ_{i+1}` is the following special case of the
canonical transition map. -/
def successiveTransitionMap {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) (i : ℕ+) :
    F.obj (Opposite.op (i + 1)) ⟶ F.obj (Opposite.op i) :=
  transitionMap F (i := i + 1) (j := i) (PNat.lt_add_right i 1).le

/-! ## The inverse limit -/

/- This is the canonical type of compatible families for the underlying
type-valued diagram.  It is Mathlib's `Functor.sections`, not a parallel limit
construction. -/
abbrev inverseLimitFamilies {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)).sections

/- The source writes the compatibility condition using only successive maps.
This set is the corresponding source-facing display. -/
def successiveCompatibleFamilies {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  {x | ∀ i : ℕ+, successiveTransitionMap F i (x (Opposite.op (i + 1))) =
    x (Opposite.op i)}

theorem inverseLimitFamilies_iff_successiveCompatibleFamilies
    {R : Type u} [Ring R] (F : NaturalInverseSystem R)
    (x : ∀ i : ℕ+ᵒᵖ, F.obj i) :
    x ∈ inverseLimitFamilies F ↔ x ∈ successiveCompatibleFamilies F := by
  sorry

/- The categorical inverse limit is the preceding chapter's canonical
`InverseSystemLimit`; `limit.isLimit` records its module-level universal
property, while the bridge below identifies its chosen object with the
compatible-family construction. -/
abbrev inverseLimitModule {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) : ModuleCat.{w} R :=
  InverseSystemLimit F

noncomputable def inverseLimitModule_isLimit {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    IsLimit (limit.cone F) :=
  limit.isLimit F

/- The chosen categorical limit is canonically equivalent to the displayed
compatible-family set.  `ModuleCat` limits are preserved by the forgetful
functor, and `Types.limitEquivSections` identifies the resulting type limit
with `Functor.sections`. -/
noncomputable def inverseLimitModule_equiv_families {R : Type u} [Ring R]
    (F : NaturalInverseSystem R) :
    (inverseLimitModule F : Type w) ≃ inverseLimitFamilies F :=
  (preservesLimitIso (CategoryTheory.forget (ModuleCat.{w} R)) F).toEquiv.trans
    (Types.limitEquivSections
      (F ⋙ CategoryTheory.forget (ModuleCat.{w} R)))

/-! ## Exactness of inverse limits -/

/- A short exact sequence of inverse systems is exact at every positive
integer.  A `ShortComplex` of functors also records the maps between the
short exact sequences and their commutativity. -/
def IsPointwiseShortExact {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R))) : Prop :=
  ∀ i : ℕ+ᵒᵖ,
    (((evaluation (ℕ+ᵒᵖ) (ModuleCat.{w} R)).obj i).mapShortComplex.obj S).ShortExact

/- Applying the inverse-limit functor to the two maps of a short complex. -/
noncomputable def inverseLimitShortComplex {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R))) :
    ShortComplex (ModuleCat.{w} R) where
  f := limMap S.f
  g := limMap S.g
  zero := by
    apply limit.hom_ext
    intro i
    simp only [Category.assoc, limMap_π, zero_comp]
    rw [← Category.assoc, limMap_π S.f i, Category.assoc,
      ← NatTrans.comp_app, S.zero]
    simp

/- This is the chapter's lemma.  Its hypotheses use Mathlib's canonical
Mittag--Leffler predicate on the underlying inverse system, which is exactly
the stabilization of the images `K_c → K_i` in the source.  The proof is the
specialization of the preceding chapter's general exactness theorem. -/
theorem inverse_limit_shortExact_of_mittagLeffler
    {R : Type u} [Ring R]
    (S : ShortComplex (InverseSystem ℕ+ (ModuleCat.{w} R)))
    (hS : IsPointwiseShortExact S)
    (hML : (S.X₁ ⋙ CategoryTheory.forget (ModuleCat.{w} R)).IsMittagLeffler) :
    (inverseLimitShortComplex S).ShortExact := by
  sorry

end

end Formalization.Books.Algebra.Unit87
