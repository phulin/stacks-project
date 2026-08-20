import Mathlib.CategoryTheory.Triangulated.Generators
import Formalization.Books.Derived.Unit35.OperationsOnFullSubcategories

/-!
# Derived Categories, Chapter 36: generators of triangulated categories

The canonical Mathlib `ObjectProperty.triangEnvelope` construction is the
source's generated subcategory.  The declarations below expose the source's
positive indexing, finite-window description, weak-generator condition, and
source-facing closure statements without duplicating Mathlib's envelope
construction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit03
open Formalization.Books.Derived.Unit04
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit35
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit36

section GeneratedSubcategories

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

/- The source only uses `⟨E⟩ₙ` for `n ≥ 1`.  The total Lean indexing below
  sends `n = 0` to Mathlib's zero-extension stage and is only unfolded at
  positive indices in the source-facing statements. -/

/-! The source's `⟨E⟩ₙ`, represented by Mathlib's canonical envelope stages. -/
abbrev generatedSubcategoryIter (E : C) (n : ℕ) : ObjectProperty C :=
  (ObjectProperty.singleton E).triangEnvelopeIter (n - 1)

/-! The source's `⟨E⟩ = ⋃ₙ ⟨E⟩ₙ`. -/
abbrev generatedSubcategory (E : C) : ObjectProperty C :=
  (ObjectProperty.singleton E).triangEnvelope

/-! The first generated stage `⟨E⟩₁`. -/
abbrev generatedSubcategoryOne (E : C) : ObjectProperty C :=
  generatedSubcategoryIter E 1

/-! The finite shift window `E[-m,m]` used in the source's explicit formula. -/
def generatorWindow (E : C) (m : ℕ) : ObjectProperty C :=
  shiftWindow (ObjectProperty.singleton E)
    (((-(m : ℤ) : ℤ) : EInt)) (((m : ℤ) : EInt))

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C] in
private lemma retractClosure_binaryProductsClosure_isClosedUnderBinaryProducts
    (P : ObjectProperty C) :
    (P.binaryProductsClosure.retractClosure).IsClosedUnderBinaryProducts := by
  refine ⟨fun X ⟨hX⟩ => ?_⟩
  choose Y hY hr using fun j => hX.prop_diag_obj j
  let f : WalkingPair → C := fun j => Y ⟨j⟩
  let fX : WalkingPair → C := fun j => hX.diag.obj ⟨j⟩
  let r : ∀ j, Retract (fX j) (f j) := fun j => Classical.choice (hr ⟨j⟩)
  have hYprod : P.binaryProductsClosure (∏ᶜ f) :=
    P.binaryProductsClosure.prop_of_isLimit (limit.isLimit _) (fun j => by
      simpa [f] using hY j)
  have hYsum : P.binaryProductsClosure (⨁ f) :=
    P.binaryProductsClosure.prop_of_iso (biproduct.isoProduct f).symm hYprod
  let hret : Retract (⨁ fX) (⨁ f) :=
    { i := biproduct.map (fun j => (r j).i)
      r := biproduct.map (fun j => (r j).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp [Category.assoc, r] }
  have hXsum : P.binaryProductsClosure.retractClosure (⨁ fX) :=
    ObjectProperty.prop_retractClosure hYsum hret
  have hXprod : P.binaryProductsClosure.retractClosure (∏ᶜ fX) :=
    P.binaryProductsClosure.retractClosure.prop_of_iso (biproduct.isoProduct _)
      hXsum
  let eF : hX.diag ≅ Discrete.functor fX := Discrete.natIsoFunctor
  let hlim : IsLimit ((Cone.postcompose eF.symm.hom).obj
      (limit.cone (Discrete.functor fX))) :=
    (IsLimit.postcomposeHomEquiv eF.symm _).symm (limit.isLimit (Discrete.functor fX))
  exact P.binaryProductsClosure.retractClosure.prop_of_iso
    (hlim.conePointUniqueUpToIso hX.isLimit) hXprod

omit [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C] in
private lemma smd_add_isClosedUnderBinaryProducts (P : ObjectProperty C) :
    (smd (add P)).IsClosedUnderBinaryProducts := by
  let : (smd (add P)).IsClosedUnderFiniteCoproducts :=
    smd_add_closedUnderDirectSums P
  refine ⟨fun X ⟨hX⟩ => ?_⟩
  let f : WalkingPair → C := fun j => hX.diag.obj ⟨j⟩
  have hsum : smd (add P) (⨁ f) :=
    (smd (add P)).prop_of_isColimit_cofan
      (biproduct.isColimit f) (fun j => hX.prop_diag_obj ⟨j⟩)
  have hprod : smd (add P) (∏ᶜ f) :=
    (smd (add P)).prop_of_iso (biproduct.isoProduct f) hsum
  let eF : hX.diag ≅ Discrete.functor f := Discrete.natIsoFunctor
  let hlim : IsLimit ((Cone.postcompose eF.symm.hom).obj
      (limit.cone (Discrete.functor f))) :=
    (IsLimit.postcomposeHomEquiv eF.symm _).symm (limit.isLimit (Discrete.functor f))
  exact (smd (add P)).prop_of_iso (hlim.conePointUniqueUpToIso hX.isLimit) hprod

omit [CategoryTheory.IsTriangulated C] in
private lemma smd_add_isClosedUnderEmptyLimits (P : ObjectProperty C) :
    (smd (add P)).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  let : (smd (add P)).IsClosedUnderFiniteCoproducts :=
    smd_add_closedUnderDirectSums P
  refine ⟨fun X ⟨hX⟩ => ?_⟩
  have hzero : smd (add P) (⊥_ C) :=
    (smd (add P)).prop_of_isInitial _ initialIsInitial
  have hzero' : smd (add P) (0 : C) :=
    (smd (add P)).prop_of_iso ((isZero_zero C).isoIsInitial initialIsInitial).symm hzero
  have hterm : IsTerminal X :=
    (isLimitEquivIsTerminalOfIsEmpty C (Cone.mk _ hX.π)).1 hX.isLimit
  exact (smd (add P)).prop_of_iso
    ((isZero_zero C).isoIsTerminal hterm) hzero'

/-! `⟨E⟩ₙ = smd(⟨E⟩₁ ⋆ ⟨E⟩ₙ₋₁)` for `n > 1`. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_succ (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E (n + 1) =
      smd (star (generatedSubcategoryOne E) (generatedSubcategoryIter E n)) := by
  simp [generatedSubcategoryIter, generatedSubcategoryOne, Unit35.star]
  change (ObjectProperty.singleton E).triangEnvelopeIter ((n + 1) - 1) =
    ObjectProperty.retractClosure
      (ObjectProperty.extensionProduct
        ((ObjectProperty.singleton E).shiftClosure ℤ).binaryProductsClosure.retractClosure
        ((ObjectProperty.singleton E).triangEnvelopeIter (n - 1)))
  rw [show (n + 1) - 1 = (n - 1) + 1 by omega]
  exact ObjectProperty.triangEnvelopeIter_succ (ObjectProperty.singleton E) (n - 1)

/-! The first stage is the source's finite-sum-and-summand closure of all shifts. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryOne_eq_smd_add_allShifts (E : C) :
    generatedSubcategoryOne E =
      smd (add (shiftWindow (ObjectProperty.singleton E)
        (⊥ : EInt) (⊤ : EInt))) := by
  let P : ObjectProperty C := ObjectProperty.singleton E
  let S : ObjectProperty C := shiftWindow P (⊥ : EInt) (⊤ : EInt)
  let B : ObjectProperty C := P.shiftClosure ℤ
  let Q : ObjectProperty C := B.binaryProductsClosure.retractClosure
  let T : ObjectProperty C := smd (add S)
  have hQT : Q ≤ T := by
    change B.binaryProductsClosure.retractClosure ≤ T
    let : T.IsClosedUnderBinaryProducts := smd_add_isClosedUnderBinaryProducts S
    let : T.IsClosedUnderLimitsOfShape (Discrete PEmpty) :=
      smd_add_isClosedUnderEmptyLimits S
    rw [ObjectProperty.retractClosure_le_iff]
    apply (ObjectProperty.binaryProductsClosure_le_iff (C := C) (P := B) (Q := T)).2
    intro X hX
    rcases hX with ⟨Y, a, e, hY⟩
    have hYE : E = Y := (ObjectProperty.singleton_iff E Y).1 hY
    subst Y
    have hS : S (E⟦a⟧) := by
      change shiftWindow P (⊥ : EInt) (⊤ : EInt) (E⟦a⟧)
      rw [shiftWindow]
      exact (ObjectProperty.prop_iSup_iff _ _).2
        ⟨⟨-a, by simp⟩, (ObjectProperty.strictMap_iff _ _ _).2
          ⟨E, (ObjectProperty.singleton_iff E E).2 rfl, by simp⟩⟩
    have hAdd : add S (E⟦a⟧) := by
      let f : Fin 1 → C := fun _ => E⟦a⟧
      refine ⟨1, f, fun _ => hS, ?_⟩
      exact ⟨(biproduct.isoCoproduct f).symm ≪≫ biproductUniqueIso f⟩
    have hT : T (E⟦a⟧) :=
      (add S).le_retractClosure (E⟦a⟧) hAdd
    exact T.prop_of_iso e.symm hT
  have hTS : T ≤ Q := by
    change smd (add S) ≤ Q
    let : Q.IsClosedUnderBinaryProducts :=
      retractClosure_binaryProductsClosure_isClosedUnderBinaryProducts B
    let : Q.IsClosedUnderLimitsOfShape (Discrete PEmpty) := by infer_instance
    let : Q.IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    have hSleB : S ≤ B := by
      intro X hX
      change shiftWindow P (⊥ : EInt) (⊤ : EInt) X at hX
      rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
      obtain ⟨i, hi⟩ := hX
      obtain ⟨Y, hY, rfl⟩ :=
        (ObjectProperty.strictMap_iff P (shiftFunctor C (-(i : ℤ))) _).1 hi
      have hYE : E = Y := (ObjectProperty.singleton_iff E Y).1 hY
      subst Y
      exact ⟨E, -(i : ℤ), Iso.refl _, (ObjectProperty.singleton_iff E E).2 rfl⟩
    have hSleQ : S ≤ Q :=
      hSleB.trans ((B.le_limitsClosure _).trans B.binaryProductsClosure.le_retractClosure)
    rw [ObjectProperty.retractClosure_le_iff]
    intro X hX
    rcases hX with ⟨r, A, hA, ⟨e⟩⟩
    have hprod : Q (∏ᶜ A) := Q.prop_product (fun i => hSleQ _ (hA i))
    have hsum : Q (⨁ A) :=
      Q.prop_of_iso (biproduct.isoProduct A).symm hprod
    have hcoprod : Q (∐ A) :=
      Q.prop_of_iso (biproduct.isoCoproduct A) hsum
    exact Q.prop_of_iso e hcoprod
  have hleft : generatedSubcategoryOne E = Q := by
    simp [generatedSubcategoryOne, generatedSubcategoryIter, Q, B, P,
      ObjectProperty.triangEnvelopeIter_zero]
  have hright : T = smd (add (shiftWindow (ObjectProperty.singleton E)
      (⊥ : EInt) (⊤ : EInt))) := by
    rfl
  rw [hleft, ← hright]
  exact le_antisymm hQT hTS

/-! Every positive stage is strictly full and stable under direct summands. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStrictlyFull (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsClosedUnderIsomorphisms := by
  infer_instance

omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStableUnderRetracts (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsStableUnderRetracts := by
  infer_instance

/-! The source's assertion that each positive stage is preserved by shifts. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_isStableUnderShifts (E : C) {n : ℕ} (_hn : 1 ≤ n) :
    (generatedSubcategoryIter E n).IsStableUnderShift ℤ := by
  infer_instance

/-! The source's assertion that each positive stage is additive. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_closedUnderFiniteDirectSums
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    ∀ (r : ℕ) (X : Fin r → C),
      (∀ i, generatedSubcategoryIter E n (X i)) →
        generatedSubcategoryIter E n (∐ X) := by
  intro r X hX
  let S := shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt)
  have hBase :
      ((ObjectProperty.singleton E).shiftClosure ℤ).binaryProductsClosure.retractClosure =
        smd (add S) := by
    simpa [S, generatedSubcategoryOne, generatedSubcategoryIter,
      ObjectProperty.triangEnvelopeIter_zero] using
      generatedSubcategoryOne_eq_smd_add_allShifts E
  have hStage : generatedSubcategoryIter E n = conePower S n := by
    change
      ObjectProperty.retractClosure
          (ObjectProperty.extensionProductIter
            ((ObjectProperty.singleton E).shiftClosure ℤ).binaryProductsClosure.retractClosure
            (n - 1)) =
        ObjectProperty.retractClosure
          (ObjectProperty.extensionProductIter (add S) (n - 1))
    rw [hBase]
    exact ObjectProperty.retractClosure_extensionProductIter_retractClosure (add S)
  rw [hStage]
  rw [hStage] at hX
  let : (conePower S n).IsClosedUnderFiniteCoproducts :=
    conePower_closedUnderDirectSums S hn
  exact (conePower S n).prop_of_isColimit_cofan
    (colimit.isColimit (Discrete.functor X)) hX

/- A fixed stage is not asserted to be closed under arbitrary cones or
   extensions; the source explicitly warns that this need not hold. -/

/-! The explicit n-fold extension-product formula for a positive stage. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategoryIter_eq_smd_starPower
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E n =
      smd (starPower (generatedSubcategoryOne E) n) := by
  conv_lhs => rw [← Nat.sub_add_cancel hn]
  simp [generatedSubcategoryIter, generatedSubcategoryOne, starPower, smd]

omit [AdditiveCategory C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [CategoryTheory.IsTriangulated C] in
private lemma shiftWindow_all_eq_iSup_generatorWindow (E : C) :
    shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt) =
      ⨆ m : {m : ℕ // 1 ≤ m}, generatorWindow E m.1 := by
  apply le_antisymm
  · intro X hX
    change shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt) X at hX
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
    obtain ⟨⟨i, hi⟩, hXi⟩ := hX
    rw [ObjectProperty.prop_iSup_iff]
    cases i with
    | ofNat k =>
        refine ⟨⟨k + 1, by omega⟩, ?_⟩
        change generatorWindow E (k + 1) X
        dsimp [generatorWindow]
        rw [shiftWindow, ObjectProperty.prop_iSup_iff]
        refine ⟨⟨(k : ℤ), ?_⟩, ?_⟩
        · constructor <;> simp; omega
        · simpa using hXi
    | negSucc k =>
        refine ⟨⟨k + 2, by omega⟩, ?_⟩
        change generatorWindow E (k + 2) X
        dsimp [generatorWindow]
        rw [shiftWindow, ObjectProperty.prop_iSup_iff]
        refine ⟨⟨Int.negSucc k, ?_⟩, ?_⟩
        · constructor <;> simp <;> omega
        · simpa using hXi
  · refine iSup_le fun m => ?_
    intro X hX
    change shiftWindow (ObjectProperty.singleton E)
      (((-(m.1 : ℤ) : ℤ) : EInt)) (((m.1 : ℤ) : EInt)) X at hX
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX ⊢
    obtain ⟨⟨i, hi⟩, hXi⟩ := hX
    exact ⟨⟨i, by simp⟩, hXi⟩

omit [AdditiveCategory C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [CategoryTheory.IsTriangulated C] in
private lemma iSup_positive_eq_iSup_succ (F : ℕ → ObjectProperty C) :
    (⨆ m : {m : ℕ // 1 ≤ m}, F m.1) = ⨆ k : ℕ, F (k + 1) := by
  apply le_antisymm
  · refine iSup_le fun m => ?_
    simpa only [Nat.sub_add_cancel m.2] using
      (le_iSup (fun k : ℕ => F (k + 1)) (m.1 - 1))
  · refine iSup_le fun k => ?_
    exact le_iSup (fun m : {m : ℕ // 1 ≤ m} => F m.1) ⟨k + 1, by omega⟩

/-! The same stage is the union over finite shift windows. -/
theorem generatedSubcategoryIter_eq_iSup_finite_windows
    (E : C) {n : ℕ} (hn : 1 ≤ n) :
    generatedSubcategoryIter E n =
      ⨆ m : {m : ℕ // 1 ≤ m},
        smd (starPower (add (generatorWindow E m.1)) n) := by
  let W : ℕ → ObjectProperty C := fun k => generatorWindow E (k + 1)
  have hU : shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt) =
      ⨆ k : ℕ, W k := by
    rw [shiftWindow_all_eq_iSup_generatorWindow,
      iSup_positive_eq_iSup_succ (fun m => generatorWindow E m)]
  rw [generatedSubcategoryIter_eq_smd_starPower E hn,
    generatedSubcategoryOne_eq_smd_add_allShifts E, hU]
  simp only [starPower, smd]
  rw [ObjectProperty.retractClosure_extensionProductIter_retractClosure]
  change smd (starPower (add (⨆ k : ℕ, W k)) n) =
    ⨆ m : {m : ℕ // 1 ≤ m},
      smd (starPower (add (generatorWindow E m.1)) n)
  rw [add_iSup W]
  rw [starPower_iSup (fun k => add (W k)) n]
  rw [smd_iSup (fun k => starPower (add (W k)) n)]
  rw [iSup_positive_eq_iSup_succ
    (fun m => smd (starPower (add (generatorWindow E m)) n))]

/-! The generated subcategory is the increasing union of the positive stages. -/
omit [CategoryTheory.IsTriangulated C] in
theorem generatedSubcategory_eq_iSup (E : C) :
    generatedSubcategory E =
      ⨆ n : {n : ℕ // 1 ≤ n}, generatedSubcategoryIter E n := by
  change (⨆ k : ℕ, (ObjectProperty.singleton E).triangEnvelopeIter k) =
    ⨆ n : {n : ℕ // 1 ≤ n},
      (ObjectProperty.singleton E).triangEnvelopeIter (n.1 - 1)
  apply le_antisymm
  · refine iSup_le fun k => ?_
    refine le_iSup (fun n : {n : ℕ // 1 ≤ n} =>
      (ObjectProperty.singleton E).triangEnvelopeIter (n.1 - 1))
      ⟨k + 1, by omega⟩
  · refine iSup_le fun n => ?_
    exact le_iSup (fun k : ℕ => (ObjectProperty.singleton E).triangEnvelopeIter k)
      (n.1 - 1)

/-! The source's combined finite-window formula for `⟨E⟩`. -/
theorem generatedSubcategory_eq_iSup_finite_windows (E : C) :
    generatedSubcategory E =
      ⨆ (n : {n : ℕ // 1 ≤ n}) (m : {m : ℕ // 1 ≤ m}),
        smd (starPower (add (generatorWindow E m.1)) n.1) := by
  sorry

/-! Concatenating positive stages adds their extension lengths. -/
theorem generatedSubcategoryIter_add
    (E : C) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    generatedSubcategoryIter E (n + n') =
      smd (star (generatedSubcategoryIter E n)
        (generatedSubcategoryIter E n')) := by
  sorry

/-!
The generated subcategory is the smallest strictly full, saturated,
triangulated subcategory containing `E`.
-/
theorem generatedSubcategory_is_smallest (E : C) :
    (generatedSubcategory E).IsClosedUnderIsomorphisms ∧
      IsSaturated (generatedSubcategory E) ∧
      (generatedSubcategory E).IsTriangulated ∧
      ObjectProperty.singleton E ≤ generatedSubcategory E ∧
      ∀ P : ObjectProperty C,
        ObjectProperty.singleton E ≤ P →
        P.IsClosedUnderIsomorphisms → P.IsTriangulated → IsSaturated P →
          generatedSubcategory E ≤ P := by
  sorry

end GeneratedSubcategories

section Generators

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [CategoryTheory.IsTriangulated C]

/- The strong and classical notions are Mathlib's canonical definitions for a
   singleton object property. -/
abbrev IsClassicalGenerator (E : C) : Prop :=
  (ObjectProperty.singleton E).IsClassicalTriangulatedGenerator

abbrev IsStrongGenerator (E : C) : Prop :=
  (ObjectProperty.singleton E).IsStrongTriangulatedGenerator

/-! The source's weak-generator condition. -/
def IsWeakGenerator (E : C) : Prop :=
  ∀ ⦃K : C⦄, ¬ IsZero K →
    ∃ (n : ℤ) (f : E ⟶ K⟦n⟧), f ≠ 0

/-! The source uses “weak generator” and “generator” synonymously. -/
abbrev IsGenerator (E : C) : Prop := IsWeakGenerator E

/-! A triangulated category has a strong generator if some object is one. -/
def HasStrongGenerator (C : Type u) [Category.{v} C] [AdditiveCategory C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C] : Prop :=
  ∃ E : C, IsStrongGenerator E

omit [CategoryTheory.IsTriangulated C] in
theorem isClassicalGenerator_iff (E : C) :
    IsClassicalGenerator E ↔ generatedSubcategory E = (⊤ : ObjectProperty C) := Iff.rfl

/-! The positive-index form of the source's strong-generator definition. -/
theorem isStrongGenerator_iff (E : C) :
    IsStrongGenerator E ↔
      ∃ n : ℕ, 1 ≤ n ∧ generatedSubcategoryIter E n = (⊤ : ObjectProperty C) := by
  sorry

/-! The source's right-orthogonal characterization. -/
theorem rightOrthogonal_iff (E K : C) :
    (∀ i : ℤ, HomIsZero E (K⟦i⟧)) ↔
      ∀ E' : C, generatedSubcategory E E' → HomIsZero E' K := by
  sorry

/-! A classical generator is a weak generator. -/
theorem classical_generator_is_generator {E : C}
    (hE : IsClassicalGenerator E) : IsGenerator E := by
  sorry

/-! If the category has a strong generator, every classical generator is strong. -/
theorem classical_generator_is_strong_generator {E : C}
    (_hC : HasStrongGenerator C)
    (_hE : IsClassicalGenerator E) : IsStrongGenerator E := by
  sorry

/-!
The source's generator-check remark.  Closure under direct summands is
represented by `smd = retractClosure` in Lean.  The displayed source
conditions imply this retract closure via split distinguished triangles,
so no extra retract hypothesis is needed here.
-/
theorem property_holds_on_generatedSubcategory
    (E : C) (P : ObjectProperty C)
    (hIso : P.IsClosedUnderIsomorphisms)
    (hFiniteSums : ∀ (r : ℕ) (X : Fin r → C),
      (∀ i, P (X i)) → P (∐ X))
    (hTriangle : ∀ (T : Triangle C), T ∈ distTriang C →
      ((P T.obj₁ ∧ P T.obj₂) → P T.obj₃) ∧
        ((P T.obj₂ ∧ P T.obj₃) → P T.obj₁) ∧
        ((P T.obj₁ ∧ P T.obj₃) → P T.obj₂))
    (hSummands : ∀ ⦃K L : C⦄, P (K ⊞ L) → P K ∧ P L)
    (hShifts : ∀ n : ℤ, P (E⟦n⟧)) :
    generatedSubcategory E ≤ P := by
  sorry

end Generators

end Formalization.Books.Derived.Unit36
