import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories

/-!
# Derived Categories, Chapter 8: the homotopy category

The source uses `Comp(𝒜)` for cochain complexes in an additive category and
`K(𝒜)` for their homotopy category.  Mathlib already supplies the canonical
cochain-complex, homotopy, quotient, and bounded-below APIs.  The bounded-above
and bounded object properties below use the same canonical support predicates
and the quotient's strict image construction.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open Formalization.Books.Homology.Unit03
open scoped ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit08

/- The source's additive-category interface supplies finite biproducts; this
   standard Mathlib bridge supplies the binary instance required by the
   homotopy-category triangulation API. -/
noncomputable instance additiveCategory_hasBinaryBiproducts
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    HasBinaryBiproducts C :=
  hasBinaryBiproducts_of_finite_biproducts C

/-! ## Complexes and their boundedness -/

/-- The source's `Comp(𝒜) = CoCh(𝒜)`, represented by integer-indexed cochain complexes. -/
abbrev Comp (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex C ℤ

/-- A cochain complex is bounded below when it is eventually zero in negative degrees. -/
abbrev IsBoundedBelow
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  CochainComplex.plus C K

/-- A cochain complex is bounded above when it is eventually zero in positive degrees. -/
def IsBoundedAbove
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  ∃ n : ℤ, K.IsStrictlyLE n

/-- A cochain complex is bounded when it is eventually zero in both directions. -/
def IsBounded
    {C : Type u} [Category.{v} C] [AdditiveCategory C] (K : Comp C) : Prop :=
  ∃ p q : ℤ, K.IsStrictlyGE p ∧ K.IsStrictlyLE q

/-- The object property of bounded-below cochain complexes. -/
abbrev boundedBelowProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  CochainComplex.plus C

/-- The object property of bounded-above cochain complexes. -/
def boundedAboveProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  fun K => IsBoundedAbove K

/-- The object property of bounded cochain complexes. -/
def boundedProperty (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (Comp C) :=
  fun K => IsBounded K

/-- The source's `Comp⁺(𝒜)`, using Mathlib's canonical full subcategory. -/
abbrev CompPlus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  CochainComplex.Plus C

/-- The source's `Comp⁻(𝒜)`, the full subcategory of bounded-above complexes. -/
abbrev CompMinus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedAboveProperty C).FullSubcategory

/-- The source's `Compᵇ(𝒜)`, the full subcategory of bounded complexes. -/
abbrev CompBounded (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedProperty C).FullSubcategory

/-! ## Homotopy categories -/

/-- The source's `K(𝒜)`, represented by Mathlib's homotopy category of cochain complexes. -/
abbrev K (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory C (.up ℤ)

/-- The bounded-below property on `K(𝒜)`, from Mathlib's homotopy-category API. -/
abbrev boundedBelowHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  HomotopyCategory.plus C

/-- The bounded-above property on `K(𝒜)`, transported along the quotient. -/
def boundedAboveHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  (boundedAboveProperty C).strictMap (HomotopyCategory.quotient C (.up ℤ))

/-- The bounded property on `K(𝒜)`, transported along the quotient. -/
def boundedHomotopyProperty
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    ObjectProperty (K C) :=
  (boundedProperty C).strictMap (HomotopyCategory.quotient C (.up ℤ))

/-- The source's `K⁺(𝒜)`, using Mathlib's canonical bounded-below homotopy category. -/
abbrev KPlus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  HomotopyCategory.Plus C

/-- The source's `K⁻(𝒜)`, the full subcategory of bounded-above homotopy objects. -/
abbrev KMinus (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedAboveHomotopyProperty C).FullSubcategory

/-- The source's `Kᵇ(𝒜)`, the full subcategory of bounded homotopy objects. -/
abbrev KBounded (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  (boundedHomotopyProperty C).FullSubcategory

/-!
The source next records that these four categories are triangulated.  The
ambient and bounded-below cases are already instances in Mathlib.  The
bounded-above and bounded cases are the two source-facing interfaces not
provided by the current Mathlib API; their proofs belong to the subsequent
cone and distinguished-triangle development.
-/

private lemma isStrictlyLE_mappingCone
    (C : Type u) [Category.{v} C] [AdditiveCategory C]
    {K L : Comp C} (f : K ⟶ L) (n₁ n₂ n : ℤ)
    [K.IsStrictlyLE n₁] [L.IsStrictlyLE n₂]
    (hn₁ : n₁ ≤ n := by lia) (hn₂ : n₂ ≤ n := by lia) :
    (CochainComplex.mappingCone f).IsStrictlyLE n := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  simp only [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n₁ _ (by lia),
    L.isZero_of_isStrictlyLE n₂ _ (by lia)⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma boundedAboveHomotopyProperty_isTriangulatedClosed₃
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedAboveHomotopyProperty C).IsTriangulatedClosed₃ := by
  refine { ext₃' := ?_ }
  intro T hT h₁ h₂
  change (boundedAboveProperty C).strictMap
    (HomotopyCategory.quotient C (.up ℤ)) T.obj₁ at h₁
  change (boundedAboveProperty C).strictMap
    (HomotopyCategory.quotient C (.up ℤ)) T.obj₂ at h₂
  obtain ⟨K₁, hK₁, hK₁'⟩ :=
    (ObjectProperty.strictMap_iff _ _ _).mp h₁
  obtain ⟨K₂, hK₂, hK₂'⟩ :=
    (ObjectProperty.strictMap_iff _ _ _).mp h₂
  obtain rfl : K₁ = T.obj₁.as := congr_arg Quotient.as hK₁'
  obtain rfl : K₂ = T.obj₂.as := congr_arg Quotient.as hK₂'
  obtain ⟨n₁, hn₁⟩ := hK₁
  obtain ⟨n₂, hn₂⟩ := hK₂
  obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
    (HomotopyCategory.quotient C (.up ℤ)).map_surjective T.mor₁
  refine ⟨_, ?_, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
    (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _)
    (Iso.refl _) ?_)⟩⟩
  · dsimp [boundedAboveHomotopyProperty]
    refine ⟨CochainComplex.mappingCone f, ?_⟩
    exact ⟨max n₁ n₂,
      isStrictlyLE_mappingCone C f n₁ n₂ (max n₁ n₂) (by simp) (by simp)⟩
  · simp [hf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma boundedHomotopyProperty_isTriangulatedClosed₃
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedHomotopyProperty C).IsTriangulatedClosed₃ := by
  refine { ext₃' := ?_ }
  intro T hT h₁ h₂
  change (boundedProperty C).strictMap
    (HomotopyCategory.quotient C (.up ℤ)) T.obj₁ at h₁
  change (boundedProperty C).strictMap
    (HomotopyCategory.quotient C (.up ℤ)) T.obj₂ at h₂
  obtain ⟨X₁, hX₁, hX₁'⟩ :=
    (ObjectProperty.strictMap_iff _ _ _).mp h₁
  obtain ⟨X₂, hX₂, hX₂'⟩ :=
    (ObjectProperty.strictMap_iff _ _ _).mp h₂
  obtain rfl : X₁ = T.obj₁.as := congr_arg Quotient.as hX₁'
  obtain rfl : X₂ = T.obj₂.as := congr_arg Quotient.as hX₂'
  obtain ⟨p₁, q₁, hp₁, hq₁⟩ := hX₁
  obtain ⟨p₂, q₂, hp₂, hq₂⟩ := hX₂
  obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ :=
    (HomotopyCategory.quotient C (.up ℤ)).map_surjective T.mor₁
  refine ⟨_, ?_, ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT
    (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _)
    (Iso.refl _) ?_)⟩⟩
  · dsimp [boundedHomotopyProperty]
    refine ⟨CochainComplex.mappingCone f, ?_⟩
    exact ⟨min (p₁ - 1) p₂, max q₁ q₂,
      ⟨CochainComplex.isStrictlyGE_mappingCone f p₁ p₂ _ (by simp) (by simp),
        isStrictlyLE_mappingCone C f q₁ q₂ _ (by simp) (by simp)⟩⟩
  · simp [hf]

noncomputable instance boundedAboveHomotopyProperty_isTriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedAboveHomotopyProperty C).IsTriangulated := by
  let hstable : (boundedAboveHomotopyProperty C).IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦
        { le_shift := by
            intro X hX
            obtain ⟨X : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
            change (boundedAboveProperty C).strictMap
              (HomotopyCategory.quotient C (.up ℤ))
              ((HomotopyCategory.quotient C (.up ℤ)).obj X) at hX
            simp only [ObjectProperty.strictMap_iff] at hX
            obtain ⟨L, hL, hLK⟩ := hX
            obtain rfl : L = X := congr_arg Quotient.as hLK
            obtain ⟨q, hq⟩ := hL
            rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
            dsimp [boundedAboveHomotopyProperty]
            refine ⟨_, ?_⟩
            exact ⟨q - n,
              CochainComplex.isStrictlyLE_shift L q n (q - n) (by lia)⟩ } }
  let hclosed₃ : (boundedAboveHomotopyProperty C).IsTriangulatedClosed₃ :=
    boundedAboveHomotopyProperty_isTriangulatedClosed₃ C
  have hclosed₂ : (boundedAboveHomotopyProperty C).IsTriangulatedClosed₂ := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    exact hclosed₃.ext₃' _ (inv_rot_of_distTriang _ hT)
      ((hstable.isStableUnderShiftBy _).le_shift _ h₃) h₁
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · exact ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        dsimp [boundedAboveHomotopyProperty]
        exact ⟨0, ⟨0, inferInstance⟩⟩⟩
  · exact hstable.isStableUnderShiftBy
  · exact hclosed₂.ext₂'

noncomputable instance boundedHomotopyProperty_isTriangulated
    (C : Type u) [Category.{v} C] [AdditiveCategory C] :
    (boundedHomotopyProperty C).IsTriangulated := by
  let hstable : (boundedHomotopyProperty C).IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦
        { le_shift := by
            intro X hX
            obtain ⟨X : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
            change (boundedProperty C).strictMap
              (HomotopyCategory.quotient C (.up ℤ))
              ((HomotopyCategory.quotient C (.up ℤ)).obj X) at hX
            simp only [ObjectProperty.strictMap_iff] at hX
            obtain ⟨L, hL, hLX⟩ := hX
            obtain rfl : L = X := congr_arg Quotient.as hLX
            obtain ⟨p, q, hp, hq⟩ := hL
            rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj]
            dsimp [boundedHomotopyProperty]
            refine ⟨_, ?_⟩
            exact ⟨p - n, q - n,
              ⟨CochainComplex.isStrictlyGE_shift L p n (p - n) (by lia),
                CochainComplex.isStrictlyLE_shift L q n (q - n) (by lia)⟩⟩ } }
  let hclosed₃ : (boundedHomotopyProperty C).IsTriangulatedClosed₃ :=
    boundedHomotopyProperty_isTriangulatedClosed₃ C
  have hclosed₂ : (boundedHomotopyProperty C).IsTriangulatedClosed₂ := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    exact hclosed₃.ext₃' _ (inv_rot_of_distTriang _ hT)
      ((hstable.isStableUnderShiftBy _).le_shift _ h₃) h₁
  refine { exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }
  · exact ⟨(HomotopyCategory.quotient C (.up ℤ)).obj 0,
      Functor.map_isZero _ (isZero_zero _), by
        dsimp [boundedHomotopyProperty]
        refine ⟨(0 : Comp C), ?_⟩
        change ∃ p q : ℤ, (0 : Comp C).IsStrictlyGE p ∧
          (0 : Comp C).IsStrictlyLE q
        exact ⟨0, 0, inferInstance, inferInstance⟩⟩
  · exact hstable.isStableUnderShiftBy
  · exact hclosed₂.ext₂'

end Formalization.Books.Derived.Unit08
