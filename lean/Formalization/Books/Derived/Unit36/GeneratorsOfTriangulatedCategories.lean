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
  have hW : Monotone W := by
    intro a b hab X hX
    change generatorWindow E (a + 1) X at hX
    change generatorWindow E (b + 1) X
    change shiftWindow (ObjectProperty.singleton E)
      (((-((a + 1 : ℕ) : ℤ) : ℤ) : EInt)) (((((a + 1 : ℕ) : ℤ) : EInt))) X at hX
    change shiftWindow (ObjectProperty.singleton E)
      (((-((b + 1 : ℕ) : ℤ) : ℤ) : EInt)) (((((b + 1 : ℕ) : ℤ) : EInt))) X
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX ⊢
    obtain ⟨⟨i, hi⟩, hXi⟩ := hX
    refine ⟨⟨i, ?_⟩, hXi⟩
    have hab' : ((a + 1 : ℕ) : ℤ) ≤ ((b + 1 : ℕ) : ℤ) := by omega
    constructor
    · rw [WithBotTop.coe_le_coe]
      exact (neg_le_neg hab').trans (WithBotTop.coe_le_coe.mp hi.1)
    · rw [WithBotTop.coe_le_coe]
      exact (WithBotTop.coe_le_coe.mp hi.2).trans hab'
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
  rw [add_iSup W hW]
  have hAdd : Monotone (fun k => add (W k)) := by
    intro a b hab X hX
    rcases hX with ⟨r, A, hA, e⟩
    exact ⟨r, A, fun i => hW hab _ (hA i), e⟩
  rw [starPower_iSup (fun k => add (W k)) hAdd n]
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
  calc
    generatedSubcategory E =
        ⨆ n : {n : ℕ // 1 ≤ n}, generatedSubcategoryIter E n.1 :=
      generatedSubcategory_eq_iSup (C := C) E
    _ = ⨆ (n : {n : ℕ // 1 ≤ n}) (m : {m : ℕ // 1 ≤ m}),
        smd (starPower (add (generatorWindow E m.1)) n.1) :=
      iSup_congr fun n => generatedSubcategoryIter_eq_iSup_finite_windows E n.2

/-! Concatenating positive stages adds their extension lengths. -/
theorem generatedSubcategoryIter_add
    (E : C) {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n') :
    generatedSubcategoryIter E (n + n') =
      smd (star (generatedSubcategoryIter E n)
        (generatedSubcategoryIter E n')) := by
  change (ObjectProperty.singleton E).triangEnvelopeIter ((n + n') - 1) =
    smd (star ((ObjectProperty.singleton E).triangEnvelopeIter (n - 1))
      ((ObjectProperty.singleton E).triangEnvelopeIter (n' - 1)))
  have hindex : (n + n') - 1 = n + (n' - 1) := by omega
  rw [hindex]
  exact ObjectProperty.triangEnvelopeIter_add (P := ObjectProperty.singleton E)
    (n := n) (m := n' - 1) (n' := n - 1) (by omega)

omit [CategoryTheory.IsTriangulated C] in
private lemma isStableUnderRetracts_of_isSaturated
    (P : ObjectProperty C) (hIso : P.IsClosedUnderIsomorphisms)
    (hSat : IsSaturated P) : P.IsStableUnderRetracts := by
  let : P.IsClosedUnderIsomorphisms := hIso
  refine ⟨?_⟩
  intro X Y r hY
  let : IsSplitMono r.i := IsSplitMono.mk' { retraction := r.r }
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle r.i
  have hmono : Mono r.i := by infer_instance
  have hmono' : Mono (Triangle.mk r.i g h).mor₁ := by
    change Mono r.i
    exact hmono
  have hzero : h = 0 :=
    (Triangle.mk r.i g h).mor₃_eq_zero_of_mono₁ hT hmono'
  obtain ⟨s, hs⟩ := distinguished_triangle_second_right_inverse hT hzero
  have hIso' : IsIso (biprod.desc r.i s) := by
    change IsIso (biprod.desc (Triangle.mk r.i g h).mor₁ s)
    exact split_triangle_biproduct_iso hT s hs
  let e : X ⊞ Z ≅ Y := @asIso _ _ _ _ (biprod.desc r.i s) hIso'
  have hsum : P (X ⊞ Z) := P.prop_of_iso e.symm hY
  have hX : P.isoClosure X := (hSat (P.le_isoClosure _ hsum)).1
  rw [ObjectProperty.isoClosure_eq_self] at hX
  exact hX

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
  have hIso : (generatedSubcategory E).IsClosedUnderIsomorphisms := by
    infer_instance
  have hSat : IsSaturated (generatedSubcategory E) := by
    let : (generatedSubcategory E).IsClosedUnderIsomorphisms := hIso
    intro X Y hXY
    rw [ObjectProperty.isoClosure_eq_self] at hXY ⊢
    exact ⟨
      ObjectProperty.IsStableUnderRetracts.of_biprod_left
        (generatedSubcategory E) hXY,
      ObjectProperty.IsStableUnderRetracts.of_biprod_right
        (generatedSubcategory E) hXY⟩
  have hTri : (generatedSubcategory E).IsTriangulated := by
    infer_instance
  refine ⟨hIso, hSat, hTri, ?_, ?_⟩
  · exact (ObjectProperty.singleton E).le_triangEnvelope
  · intro P hP hPI hPT hPS
    let : P.IsClosedUnderIsomorphisms := hPI
    let : P.IsTriangulated := hPT
    let : P.IsStableUnderRetracts :=
      isStableUnderRetracts_of_isSaturated P hPI hPS
    exact (ObjectProperty.triangEnvelope_le_iff
      (P := ObjectProperty.singleton E) (Q := P)).2 hP

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
omit [CategoryTheory.IsTriangulated C] in
theorem isStrongGenerator_iff (E : C) :
    IsStrongGenerator E ↔
      ∃ n : ℕ, 1 ≤ n ∧ generatedSubcategoryIter E n = (⊤ : ObjectProperty C) := by
  change (∃ n : ℕ,
      (ObjectProperty.singleton E).triangEnvelopeIter n = (⊤ : ObjectProperty C)) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, by omega, ?_⟩
    change (ObjectProperty.singleton E).triangEnvelopeIter ((n + 1) - 1) = ⊤
    simpa using hn
  · rintro ⟨n, hn, hN⟩
    refine ⟨n - 1, ?_⟩
    change (ObjectProperty.singleton E).triangEnvelopeIter (n - 1) = ⊤ at hN
    exact hN

/-! The source's right-orthogonal characterization. -/
omit [CategoryTheory.IsTriangulated C] in
theorem rightOrthogonal_iff (E K : C) :
    (∀ i : ℤ, HomIsZero E (K⟦i⟧)) ↔
      ∀ E' : C, generatedSubcategory E E' → HomIsZero E' K := by
  constructor
  · intro hEK
    let Q : ObjectProperty C :=
      ((ObjectProperty.singleton K).shiftClosure ℤ).leftOrthogonal
    have hQiso : Q.IsClosedUnderIsomorphisms := by
      dsimp [Q]
      infer_instance
    have hQtri : Q.IsTriangulated := by
      dsimp [Q]
      infer_instance
    have hQsat : IsSaturated Q := by
      let : Q.IsClosedUnderIsomorphisms := hQiso
      intro X Y hXY
      rw [ObjectProperty.isoClosure_eq_self] at hXY ⊢
      constructor
      · change ∀ ⦃Z : C⦄ (f : X ⟶ Z),
          (ObjectProperty.singleton K).shiftClosure ℤ Z → f = 0
        intro Z f hZ
        have hzero : biprod.desc f (0 : Y ⟶ Z) = 0 :=
          hXY (biprod.desc f (0 : Y ⟶ Z)) hZ
        simpa using congrArg
          (fun q : (X ⊞ Y) ⟶ Z => (biprod.inl : X ⟶ X ⊞ Y) ≫ q) hzero
      · change ∀ ⦃Z : C⦄ (f : Y ⟶ Z),
          (ObjectProperty.singleton K).shiftClosure ℤ Z → f = 0
        intro Z f hZ
        have hzero : biprod.desc (0 : X ⟶ Z) f = 0 :=
          hXY (biprod.desc (0 : X ⟶ Z) f) hZ
        simpa using congrArg
          (fun q : (X ⊞ Y) ⟶ Z => (biprod.inr : Y ⟶ X ⊞ Y) ≫ q) hzero
    have hE : ObjectProperty.singleton E ≤ Q := by
      intro X hX
      obtain rfl := (ObjectProperty.singleton_iff E X).1 hX
      change ∀ ⦃Z : C⦄ (f : E ⟶ Z),
        (ObjectProperty.singleton K).shiftClosure ℤ Z → f = 0
      intro Z f hZ
      obtain ⟨Y, a, e, hY⟩ := hZ
      obtain rfl := (ObjectProperty.singleton_iff K Y).1 hY
      apply (cancel_mono e.hom).1
      simpa using hEK a (f ≫ e.hom)
    have hgen : generatedSubcategory E ≤ Q := by
      let : Q.IsClosedUnderIsomorphisms := hQiso
      let : Q.IsTriangulated := hQtri
      let : Q.IsStableUnderRetracts :=
        isStableUnderRetracts_of_isSaturated Q hQiso hQsat
      exact (ObjectProperty.triangEnvelope_le_iff
        (P := ObjectProperty.singleton E) (Q := Q)).2 hE
    intro E' hE'
    change ∀ f : E' ⟶ K, f = 0
    intro f
    have hE'Q : Q E' := hgen E' hE'
    change ∀ ⦃Z : C⦄ (g : E' ⟶ Z),
      (ObjectProperty.singleton K).shiftClosure ℤ Z → g = 0 at hE'Q
    have hKshift : (ObjectProperty.singleton K).shiftClosure ℤ K :=
      (ObjectProperty.le_shiftClosure (A := ℤ) (ObjectProperty.singleton K)) K
        ((ObjectProperty.singleton_iff K K).2 rfl)
    exact hE'Q (Z := K) f hKshift
  · intro hE' i f
    obtain ⟨g, rfl⟩ :=
      ((shiftEquiv C i).symm.toAdjunction.homEquiv _ _).surjective f
    have hEgen : generatedSubcategory E E := by
      exact (ObjectProperty.singleton E).le_triangEnvelope E
        ((ObjectProperty.singleton_iff E E).2 rfl)
    have hStable : (generatedSubcategory E).IsStableUnderShift ℤ := inferInstance
    have hshift : generatedSubcategory E (E⟦(-i : ℤ)⟧) :=
      (hStable.isStableUnderShiftBy (-i)).le_shift _ hEgen
    let : (shiftEquiv C i).symm.functor.Additive := by
      change (shiftFunctor C (-i)).Additive
      infer_instance
    let : (shiftEquiv C i).symm.inverse.Additive := by
      change (shiftFunctor C i).Additive
      infer_instance
    have hg : g = 0 := hE' _ hshift g
    have hzero :
        ((shiftEquiv C i).symm.toAdjunction.homEquiv E K) 0 = 0 := by
      rw [Adjunction.homEquiv_unit]
      simp
    rw [hg]
    exact hzero

/-! A classical generator is a weak generator. -/
omit [CategoryTheory.IsTriangulated C] in
theorem classical_generator_is_generator {E : C}
    (hE : IsClassicalGenerator E) : IsGenerator E := by
  intro K hK
  by_contra h
  have horth : ∀ i : ℤ, HomIsZero E (K⟦i⟧) := by
    intro i f
    by_contra hf
    exact h ⟨i, f, hf⟩
  have hgenEq : generatedSubcategory E = (⊤ : ObjectProperty C) :=
    (isClassicalGenerator_iff E).1 hE
  have hgen : generatedSubcategory E K := by
    rw [hgenEq]
    trivial
  have hz : (𝟙 K) = 0 :=
    ((rightOrthogonal_iff E K).1 horth) K hgen (𝟙 K)
  exact hK ((IsZero.iff_id_eq_zero K).2 hz)

/-! If the category has a strong generator, every classical generator is strong. -/
theorem classical_generator_is_strong_generator {E : C}
    (_hC : HasStrongGenerator C)
    (_hE : IsClassicalGenerator E) : IsStrongGenerator E := by
  obtain ⟨F, hF⟩ := _hC
  rw [isStrongGenerator_iff F] at hF
  obtain ⟨n, hn, hFn⟩ := hF
  have hFgen : generatedSubcategory E F := by
    rw [(isClassicalGenerator_iff E).1 _hE]
    trivial
  rw [generatedSubcategory_eq_iSup E, ObjectProperty.prop_iSup_iff] at hFgen
  obtain ⟨m, hm⟩ := hFgen
  change generatedSubcategoryIter E (m : ℕ) F at hm
  have hmpos : 1 ≤ (m : ℕ) := m.2
  have hsingleton : ObjectProperty.singleton F ≤ generatedSubcategoryIter E (m : ℕ) := by
    intro X hX
    have hFX : F = X := (ObjectProperty.singleton_iff F X).1 hX
    subst X
    exact hm
  have htransfer : ∀ k : ℕ, 1 ≤ k →
      generatedSubcategoryIter F k ≤ generatedSubcategoryIter E ((m : ℕ) * k) := by
    let Q : ObjectProperty C := generatedSubcategoryIter E (m : ℕ)
    have hQshift : Q.IsStableUnderShift ℤ :=
      generatedSubcategoryIter_isStableUnderShifts E hmpos
    let : Q.IsStableUnderRetracts :=
      generatedSubcategoryIter_isStableUnderRetracts E hmpos
    have hFQ : Q F := hsingleton F ((ObjectProperty.singleton_iff F F).2 rfl)
    have hWindow :
        shiftWindow (ObjectProperty.singleton F) (⊥ : EInt) (⊤ : EInt) ≤ Q := by
      intro X hX
      change shiftWindow (ObjectProperty.singleton F) (⊥ : EInt) (⊤ : EInt) X at hX
      rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
      obtain ⟨i, hi⟩ := hX
      obtain ⟨Y, hY, rfl⟩ :=
        (ObjectProperty.strictMap_iff (ObjectProperty.singleton F)
          (shiftFunctor C (-(i : ℤ))) _).1 hi
      have hFY : F = Y := (ObjectProperty.singleton_iff F Y).1 hY
      subst Y
      have hshift :=
        (hQshift.isStableUnderShiftBy (-(i : ℤ))).le_shift _ hFQ
      exact (ObjectProperty.prop_shift_iff Q _ _).1 hshift
    have hAdd : add
        (shiftWindow (ObjectProperty.singleton F) (⊥ : EInt) (⊤ : EInt)) ≤ Q := by
      intro X hX
      rcases hX with ⟨r, A, hA, ⟨e⟩⟩
      have hsum : Q (∐ A) :=
        (generatedSubcategoryIter_closedUnderFiniteDirectSums E hmpos) r A
          (fun i => hWindow (A i) (hA i))
      exact Q.prop_of_iso e hsum
    have hOne : generatedSubcategoryOne F ≤ Q := by
      rw [generatedSubcategoryOne_eq_smd_add_allShifts F]
      rw [ObjectProperty.retractClosure_le_iff]
      exact hAdd
    intro k
    induction k with
    | zero =>
        intro hk
        omega
    | succ k ih =>
        intro hk
        cases k with
        | zero =>
            simpa using hOne
        | succ k =>
            have hk' : 1 ≤ k + 1 := by omega
            rw [generatedSubcategoryIter_succ F hk']
            have hrewrite :
                (m : ℕ) * (k + 1 + 1) =
                  (m : ℕ) + (m : ℕ) * (k + 1) := by
              calc
                (m : ℕ) * (k + 1 + 1) =
                    (m : ℕ) * (k + 1) + (m : ℕ) := by
                      rw [Nat.mul_succ]
                _ = (m : ℕ) + (m : ℕ) * (k + 1) := by ac_rfl
            rw [hrewrite]
            have hmk : 1 ≤ (m : ℕ) * (k + 1) :=
              Nat.mul_pos hmpos (by omega)
            rw [generatedSubcategoryIter_add E hmpos hmk]
            apply ObjectProperty.monotone_retractClosure
            exact
              (ObjectProperty.monotone_extensionProduct_left
                (generatedSubcategoryIter F (k + 1)) hOne).trans
                (ObjectProperty.monotone_extensionProduct_right
                  (generatedSubcategoryIter E (m : ℕ)) (ih (by omega)))
  have htop : (⊤ : ObjectProperty C) ≤
      generatedSubcategoryIter E ((m : ℕ) * n) := by
    rw [← hFn]
    exact htransfer n hn
  have hEq : generatedSubcategoryIter E ((m : ℕ) * n) = (⊤ : ObjectProperty C) :=
    le_antisymm le_top htop
  exact (isStrongGenerator_iff E).2
    ⟨(m : ℕ) * n, Nat.mul_pos hmpos hn, hEq⟩

/-!
The source's generator-check remark.  Closure under direct summands is
represented by `smd = retractClosure` in Lean.  The displayed source
conditions imply this retract closure via split distinguished triangles,
so no extra retract hypothesis is needed here.
-/
omit [CategoryTheory.IsTriangulated C] in
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
  have hSat : IsSaturated P := by
    let : P.IsClosedUnderIsomorphisms := hIso
    intro X Y hXY
    rw [ObjectProperty.isoClosure_eq_self] at hXY ⊢
    exact hSummands hXY
  let : P.IsStableUnderRetracts :=
    isStableUnderRetracts_of_isSaturated P hIso hSat
  have hWindow :
      shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt) ≤ P := by
    intro X hX
    change shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt) X at hX
    rw [shiftWindow, ObjectProperty.prop_iSup_iff] at hX
    obtain ⟨i, hi⟩ := hX
    obtain ⟨Y, hY, rfl⟩ :=
      (ObjectProperty.strictMap_iff (ObjectProperty.singleton E)
        (shiftFunctor C (-(i : ℤ))) _).1 hi
    have hEY : E = Y := (ObjectProperty.singleton_iff E Y).1 hY
    subst Y
    simpa using hShifts (-(i : ℤ))
  have hAdd : add
      (shiftWindow (ObjectProperty.singleton E) (⊥ : EInt) (⊤ : EInt)) ≤ P := by
    intro X hX
    rcases hX with ⟨r, A, hA, ⟨e⟩⟩
    have hsum : P (∐ A) :=
      hFiniteSums r A (fun i => hWindow (A i) (hA i))
    exact P.prop_of_iso e hsum
  have hOne : generatedSubcategoryOne E ≤ P := by
    rw [generatedSubcategoryOne_eq_smd_add_allShifts E]
    rw [ObjectProperty.retractClosure_le_iff]
    exact hAdd
  have hstage : ∀ n : ℕ, 1 ≤ n → generatedSubcategoryIter E n ≤ P := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn
        cases n with
        | zero =>
            simpa using hOne
        | succ n =>
            have hn' : 1 ≤ n + 1 := by omega
            rw [generatedSubcategoryIter_succ E hn']
            rw [ObjectProperty.retractClosure_le_iff]
            intro X hX
            change ObjectProperty.extensionProduct
              (generatedSubcategoryOne E)
              (generatedSubcategoryIter E (n + 1)) X at hX
            rw [ObjectProperty.extensionProduct_iff] at hX
            obtain ⟨Y, Z, f, g, h, hT, hY, hZ⟩ := hX
            exact (hTriangle _ hT).2.2 ⟨hOne Y hY, ih (by omega) Z hZ⟩
  rw [generatedSubcategory_eq_iSup E]
  refine iSup_le ?_
  intro n
  exact hstage n n.2

end Generators

end Formalization.Books.Derived.Unit36
