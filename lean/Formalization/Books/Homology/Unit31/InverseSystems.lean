import Formalization.Books.Categories.Unit22.EssentiallyConstantSystems
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Formalization.Books.Homology.Unit13.Complexes
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Data.PNat.Basic
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Homological Algebra, Chapter 31: Inverse systems

The source indexes inverse systems by the positive natural numbers.  They are
represented by the canonical functor category `InverseSystem ℕ+ C`; its
transition maps, limits, pointwise exactness, and essentially constant systems
are all expressed through the existing categorical APIs.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit21
open Formalization.Books.Categories.Unit22
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit13
open scoped ZeroObject

universe u v w

namespace Formalization.Books.Homology.Unit31

/-! ## Inverse systems over the positive integers -/

/- The positive integers are the source's indexing set
`\mathbf{N} = \{1,2,3,\ldots\}`. -/
abbrev NatInverseSystem (C : Type u) [Category.{v} C] :=
  InverseSystem ℕ+ C

/- A map from the `i`-th stage to the `j`-th stage for `j ≤ i`. -/
def transitionMap {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) {i j : ℕ+} (h : j ≤ i) :
    F.obj (Opposite.op i) ⟶ F.obj (Opposite.op j) :=
  F.map (opHomOfLE h)

@[simp] theorem transitionMap_refl {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (i : ℕ+) :
    transitionMap F (i := i) (j := i) le_rfl = 𝟙 (F.obj (Opposite.op i)) := by
  simp [transitionMap, opHomOfLE]

/- Functoriality is the source's identity and composition condition for the
transition maps. -/
theorem transitionMap_comp {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C)
    {i j k : ℕ+} (hij : j ≤ i) (hjk : k ≤ j) :
    transitionMap F (i := i) (j := j) hij ≫
        transitionMap F (i := j) (j := k) hjk =
      transitionMap F (i := i) (j := k) (hjk.trans hij) := by
  change F.map (homOfLE hij).op ≫ F.map (homOfLE hjk).op =
    F.map (homOfLE (hjk.trans hij)).op
  rw [← F.map_comp, ← op_comp, homOfLE_comp]

/- The displayed adjacent transition map `φᵢ` is a special case of the
canonical map above. -/
def successiveTransitionMap {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) (i : ℕ+) :
    F.obj (Opposite.op (i + 1)) ⟶ F.obj (Opposite.op i) :=
  transitionMap F (i := i + 1) (j := i) (PNat.lt_add_right i 1).le

/- Morphisms of inverse systems are natural transformations, and the category
instance is the canonical functor-category instance. -/
abbrev inverseSystemEvaluation {C : Type u} [Category.{v} C] (i : ℕ+ᵒᵖ) :
    NatInverseSystem C ⥤ C :=
  (evaluation (ℕ+ᵒᵖ) C).obj i

/- The source's additive-category structure is the established project
interface, while the underlying preadditive and finite-product structures are
inherited componentwise from the functor category. -/
@[instance_reducible] def inverseSystemAdditiveCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    AdditiveCategory (NatInverseSystem C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

instance inverseSystem_additiveCategory
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    AdditiveCategory (NatInverseSystem C) :=
  inverseSystemAdditiveCategory C

/- Mathlib's functor-category construction supplies the abelian structure. -/
instance inverseSystem_abelian
    (C : Type u) [Category.{v} C] [Abelian C] :
    Abelian (NatInverseSystem C) := by
  infer_instance

/- The source's assertion that exactness is pointwise is recorded with the
canonical evaluation functors. -/
theorem inverseSystem_exact_iff_pointwise
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (NatInverseSystem C)) :
    S.Exact ↔
      ∀ i : ℕ+ᵒᵖ,
        (((evaluation (ℕ+ᵒᵖ) C).obj i).mapShortComplex.obj S).Exact := by
  sorry

/-! ## Limits and compatible families -/

/- This is the source's `limᵢ Mᵢ`; the construction is the canonical limit
of the inverse-system diagram. -/
abbrev inverseSystemLimit {I : Type u} [Preorder I]
    {C : Type v} [Category.{w} C]
    (F : InverseSystem I C) [HasLimit F] : C :=
  InverseSystemLimit F

noncomputable def inverseSystemLimitIsLimit
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) [HasLimit F] : IsLimit (limit.cone F) :=
  limit.isLimit F

/- In `Type`, a limit is canonically equivalent to the set of compatible
families, and the following unfolds the compatibility condition used in the
source's product description. -/
abbrev inverseLimitFamilies
    (F : NatInverseSystem (Type u)) :
    Set (∀ i : ℕ+ᵒᵖ, F.obj i) :=
  F.sections

theorem inverseLimitFamilies_iff
    (F : NatInverseSystem (Type u))
    (x : ∀ i : ℕ+ᵒᵖ, F.obj i) :
    x ∈ inverseLimitFamilies F ↔
      ∀ {i j : ℕ+ᵒᵖ} (f : i ⟶ j), F.map f (x i) = x j := by
  rfl

/- The same compatible-family description for inverse systems of abelian
groups is obtained after applying the canonical forgetful functor. -/
abbrev additiveGroupInverseLimitFamilies
    (F : NatInverseSystem AddCommGrpCat) :
    Set (∀ i : ℕ+ᵒᵖ, (F.obj i : Type)) :=
  (F ⋙ CategoryTheory.forget AddCommGrpCat).sections

theorem additiveGroupInverseLimitFamilies_iff
    (F : NatInverseSystem AddCommGrpCat)
    (x : ∀ i : ℕ+ᵒᵖ, (F.obj i : Type)) :
    x ∈ additiveGroupInverseLimitFamilies F ↔
      ∀ {i j : ℕ+ᵒᵖ} (f : i ⟶ j),
        (F.map f).hom (x i) = x j := by
  rfl

noncomputable def inverseSystemTypeLimitEquivSections
    (F : NatInverseSystem (Type u)) :
    (inverseSystemLimit F : Type u) ≃ inverseLimitFamilies F :=
  Types.limitEquivSections F

/-! ## The Mittag--Leffler condition -/

/- In an arbitrary abelian category, the image of a transition map is a
subobject of the target.  This is the categorical form of the source's
stabilization condition. -/
def IsMittagLeffler
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C) : Prop :=
  ∀ i : ℕ+, ∃ c : ℕ+, ∃ h : i ≤ c,
    ∀ k : ℕ+, ∀ h' : c ≤ k,
      imageSubobject (F.map (opHomOfLE h)) =
        imageSubobject (F.map (opHomOfLE (h.trans h')))

/- Mathlib's canonical `Functor.IsMittagLeffler` is the underlying-set
formulation.  This bridge records its equivalence with the abelian image
formulation for the abelian groups used by the subsequent exactness lemmas. -/
theorem isMittagLeffler_iff_underlying
    (F : NatInverseSystem AddCommGrpCat) :
    IsMittagLeffler F ↔
      (F ⋙ CategoryTheory.forget AddCommGrpCat).IsMittagLeffler := by
  sorry

/-! ## Exactness after taking inverse limits -/

noncomputable def inverseSystemLimitMap
    {C : Type u} [Category.{v} C]
    {F G : NatInverseSystem C} [HasLimit F] [HasLimit G]
    (f : F ⟶ G) : inverseSystemLimit F ⟶ inverseSystemLimit G :=
  limMap f

/- These are the two finite presentations of the source's displayed exact
sequences. -/
noncomputable def inverseSystemLimitSequence
    (S : ShortComplex (NatInverseSystem AddCommGrpCat)) :
    ComposableArrows AddCommGrpCat 3 :=
  ComposableArrows.mk₃
    (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
    (inverseSystemLimitMap S.f)
    (inverseSystemLimitMap S.g)

noncomputable def inverseSystemLimitShortExactSequence
    (S : ShortComplex (NatInverseSystem AddCommGrpCat)) :
    ComposableArrows AddCommGrpCat 4 :=
  ComposableArrows.mk₄
    (0 : (0 : AddCommGrpCat) ⟶ inverseSystemLimit S.X₁)
    (inverseSystemLimitMap S.f)
    (inverseSystemLimitMap S.g)
    (0 : inverseSystemLimit S.X₃ ⟶ (0 : AddCommGrpCat))

theorem inverseSystemLimit_exact
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact) :
    (inverseSystemLimitSequence S).Exact := by
  sorry

theorem inverseSystemLimit_mittagLeffler_quotient
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hML : IsMittagLeffler S.X₂) :
    IsMittagLeffler S.X₃ := by
  sorry

theorem inverseSystemLimit_exact_of_mittagLeffler
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hML : IsMittagLeffler S.X₁) :
    (inverseSystemLimitShortExactSequence S).Exact := by
  sorry

theorem inverseSystemLimit_exact_of_exact_of_mittagLeffler
    (S : ComposableArrows (NatInverseSystem AddCommGrpCat) 3)
    (hS : S.Exact)
    (hML : IsMittagLeffler (S.obj' 0)) :
    (ComposableArrows.mk₂
      (inverseSystemLimitMap (S.map' 1 2))
      (inverseSystemLimitMap (S.map' 2 3))).Exact := by
  sorry

/-! ## Essentially constant systems -/

/- This is the canonical definition from Categories, Chapter 22, specialized
to the positive-integer inverse-system index. -/
abbrev IsEssentiallyConstant
    {C : Type u} [Category.{v} C]
    (F : NatInverseSystem C) : Prop :=
  Formalization.Books.Categories.Unit22.IsEssentiallyConstantInverseSystem F

/- The source's direct-sum decomposition is written with biproducts.  The
maps `z` are the induced maps on the complementary summands; compatibility
means that every transition map is the identity on the limit summand and is
`z` on the complementary summand. -/
theorem essentiallyConstant_iff_biproduct_decomposition
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C) [HasLimit F] :
    IsEssentiallyConstant F ↔
      ∃ (i : ℕ+) (Z : ℕ+ → C)
        (e : ∀ j : ℕ+, i ≤ j →
          @CategoryTheory.Iso C _
            (@CategoryTheory.Limits.biprod C _ _ (inverseSystemLimit F) (Z j) _)
            (F.obj (Opposite.op j)))
        (z : ∀ {j j' : ℕ+}, j ≤ j' →
          @Quiver.Hom C _ (Z j') (Z j)),
        (∀ {j j' : ℕ+} (hij : i ≤ j) (hij' : i ≤ j') (h : j ≤ j'),
          (e j' hij').hom ≫ transitionMap F h ≫ (e j hij).inv =
            biprod.map (𝟙 _) (z h)) ∧
        (∀ j : ℕ+, ∃ (j' : ℕ+) (h : j ≤ j'), z h = 0) := by
  sorry

theorem essentiallyConstant_isMittagLeffler
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : NatInverseSystem C)
    (hF : IsEssentiallyConstant F) :
    IsMittagLeffler F := by
  sorry

theorem mittagLeffler_iff_of_essentiallyConstant_quotient
    (S : ShortComplex (NatInverseSystem AddCommGrpCat))
    (hS : S.ShortExact)
    (hC : IsEssentiallyConstant S.X₃) :
    IsMittagLeffler S.X₁ ↔ IsMittagLeffler S.X₂ := by
  sorry

/-! ## Cohomology of inverse systems of complexes -/

abbrev InverseSystemOfCochainComplexes :=
  NatInverseSystem (CochainComplex AddCommGrpCat ℤ)

abbrev inverseSystemComplexComponent
    (K : InverseSystemOfCochainComplexes) (n : ℤ) :
    NatInverseSystem AddCommGrpCat :=
  K ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n

abbrev inverseSystemCohomologySystem
    (K : InverseSystemOfCochainComplexes) (n : ℤ) :
    NatInverseSystem AddCommGrpCat :=
  K ⋙ Formalization.Books.Homology.Unit13.cochainCohomologyFunctor
    AddCommGrpCat n

theorem inverseSystem_cohomology_zero_iso_limit
    (K : InverseSystemOfCochainComplexes)
    (hA₂ : IsMittagLeffler (inverseSystemComplexComponent K (-2)))
    (hA₁ : IsMittagLeffler (inverseSystemComplexComponent K (-1)))
    (hH₁ : IsEssentiallyConstant (inverseSystemCohomologySystem K (-1))) :
    Nonempty
      ((inverseSystemLimit K).homology 0 ≅
        inverseSystemLimit (inverseSystemCohomologySystem K 0)) := by
  sorry

/-! ## Inverse systems over ordinals -/

abbrev OrdinalInverseSystemOfCochainComplexes (α : Ordinal) :=
  InverseSystem (Set.Iio α) (CochainComplex AddCommGrpCat ℤ)

/- The inclusion of the stages below `β` into the stages below `α`. -/
def ordinalIioEmbedding {α : Ordinal} (β : Set.Iio α) :
    Set.Iio β.1 →o Set.Iio α :=
  { toFun := fun γ =>
      ⟨γ.1, lt_trans (show γ.1 < β.1 from γ.2) (show β.1 < α from β.2)⟩
    monotone' := fun _ _ h => h }

def ordinalIioInclusion {α : Ordinal} (β : Set.Iio α) :
    Set.Iio β.1 ⥤ Set.Iio α :=
  (ordinalIioEmbedding β).monotone.functor

/- The restriction of the ordinal-indexed system to the stages below `β`. -/
abbrev ordinalPrefixSystem {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α) (β : Set.Iio α) :
    InverseSystem (Set.Iio β.1) (CochainComplex AddCommGrpCat ℤ) :=
  (ordinalIioInclusion β).op ⋙ K

abbrev ordinalPrefixComponent {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α) (β : Set.Iio α) (n : ℤ) :
    InverseSystem (Set.Iio β.1) AddCommGrpCat :=
  ordinalPrefixSystem K β ⋙
    HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) n

/- The canonical map from the `β`-th component to the limit of all earlier
components. -/
def ordinalPrefixIndexMap {α : Ordinal}
    (β : Set.Iio α) (γ : (Set.Iio β.1)ᵒᵖ) :
    Opposite.op β ⟶
      Opposite.op ((ordinalIioInclusion β).obj γ.unop) :=
  let hγ : (ordinalIioEmbedding β) γ.unop < β := by
    exact γ.unop.property
  (homOfLE hγ.le).op

noncomputable def ordinalPrefixCone {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α)
    (β : Set.Iio α) (n : ℤ) :
    Cone (ordinalPrefixComponent K β n) where
  pt := (K.obj (Opposite.op β)).X n
  π :=
    { app := fun γ => (K.map (ordinalPrefixIndexMap β γ)).f n
      naturality := by
        intro γ γ' f
        change
          (K.map (ordinalPrefixIndexMap β γ')).f n =
            (K.map (ordinalPrefixIndexMap β γ)).f n ≫
              (K.map ((ordinalIioInclusion β).op.map f)).f n
        rw [← HomologicalComplex.comp_f, ← K.map_comp]
        congr 1 }

noncomputable def ordinalPrefixMap {α : Ordinal}
    (K : OrdinalInverseSystemOfCochainComplexes α)
    (β : Set.Iio α) (n : ℤ) :
    (K.obj (Opposite.op β)).X n ⟶
      inverseSystemLimit (ordinalPrefixComponent K β n) :=
  limit.lift (ordinalPrefixComponent K β n) (ordinalPrefixCone K β n)

theorem acyclic_limit_of_ordinal_inverse_system
    (α : Ordinal) (K : OrdinalInverseSystemOfCochainComplexes α)
    (hacyclic : ∀ β : Set.Iio α, (K.obj (Opposite.op β)).Acyclic)
    (hsurjective : ∀ (β : Set.Iio α) (n : ℤ),
      Function.Surjective (ordinalPrefixMap K β n)) :
    (inverseSystemLimit K).Acyclic := by
  sorry

/- The source's proof-only constructions of the systems of cycles and images
are already represented by the canonical kernel/image and homology APIs used
in the cohomology theorem above; they need no additional public declarations.
The warning that ML need not suffice in arbitrary AB4* abelian categories is
recorded by the hypotheses of the exactness declarations, which specialize
the positive result to abelian groups as in the source. -/

end Formalization.Books.Homology.Unit31
