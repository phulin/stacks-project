import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Algebra.Category.Grp.Colimits
import Formalization.Books.Derived.Unit33.DerivedColimits
import Formalization.Books.Derived.Unit36.GeneratorsOfTriangulatedCategories

/-!
# Derived Categories, Chapter 37: compact objects

The source's compactness condition is expressed by the canonical coproduct
comparison for a representable additive functor.  Homotopy colimits use the
`IsDerivedColimit` interface from Chapter 33, while finite generated
subcategories and weak generators use the Chapter 36 interfaces.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit36
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u

namespace Formalization.Books.Derived.Unit37

section CompactObjects

variable {C : Type u} [Category.{v} C] [AdditiveCategory C]
  [HasCoproducts.{v} C]

/-! The coproduct comparison formulation of a compact object. -/
def IsCompactObject (K : C) : Prop :=
  ∀ (I : Type v) (E : I → C),
    IsIso (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) E)

/-! The object property cut out by compact objects. -/
def compactObjects : ObjectProperty C :=
  fun K => IsCompactObject K

/-!
The all-coproduct compactness condition implies the countable version used by
the Chapter 33 homotopy-colimit interface.
-/
theorem isCountablyCompact_of_isCompactObject
    [HasCountableCoproducts C] (K : C) (hK : IsCompactObject K) :
    IsCountablyCompact K := by
  let F := preadditiveCoyoneda.obj (Opposite.op K)
  let _ : PreservesColimitsOfShape (Discrete (ULift.{v} ℕ)) F :=
    ⟨fun {K} => by
      let f : ULift.{v} ℕ → C := fun i => K.obj (Discrete.mk i)
      let _ : IsIso (sigmaComparison F f) := hK (ULift.{v} ℕ) f
      let _ : PreservesColimit (Discrete.functor f) F :=
        PreservesCoproduct.of_iso_comparison F f
      exact preservesColimit_of_iso_diagram F
        (Discrete.natIso (fun j => Iso.refl (K.obj j)) :
          Discrete.functor f ≅ K)⟩
  let _ : PreservesColimitsOfShape (Discrete ℕ) F :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.ulift : ULift.{v} ℕ ≃ ℕ)) F
  intro E
  change IsIso (sigmaComparison F E)
  infer_instance

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-!
Compact objects form the source's strictly full, saturated,
(pre-)triangulated subcategory.  `IsSaturated` is the established
object-property encoding of closure under direct summands (the Karoubian
part of the source's terminology).
-/
theorem compactObjects_is_strictlyFull_saturated_pretriangulated :
    (compactObjects (C := C)).IsClosedUnderIsomorphisms ∧
      (compactObjects (C := C)).IsTriangulated ∧
      IsSaturated (compactObjects (C := C)) := by
  sorry

/-! The full subcategory of compact objects is Karoubian. -/
theorem compactObjects_fullSubcategory_isKaroubian :
    IsIdempotentComplete (compactObjects (C := C)).FullSubcategory := by
  let _ : IsIdempotentComplete C :=
    Formalization.Books.Derived.Unit04.karoubian_of_countable_coproducts
  let P : ObjectProperty C := compactObjects (C := C)
  have hP := compactObjects_is_strictlyFull_saturated_pretriangulated (C := C)
  refine ⟨?_⟩
  intro X p hp
  have hp' : p.hom ≫ p.hom = p.hom := by
    simpa using congrArg (fun f => f.hom) hp
  obtain ⟨Y, i, e, hie, hei⟩ :=
    IsIdempotentComplete.idempotents_split X.obj p.hom hp'
  let q : X.obj ⟶ X.obj := 𝟙 _ - p.hom
  have hq : q ≫ q = q := by
    dsimp [q]
    simp [sub_comp, comp_sub, hp']
  obtain ⟨Z, j, d, hjd, hdj⟩ :=
    IsIdempotentComplete.idempotents_split X.obj q hq
  let a : Y ⊞ Z ⟶ X.obj := biprod.desc i j
  let b : X.obj ⟶ Y ⊞ Z := biprod.lift e d
  have hab : b ≫ a = 𝟙 _ := by
    dsimp [a, b]
    simp [hei, hdj, q]
  have hqd : q ≫ d = d := by
    rw [← hdj, Category.assoc, hjd, Category.comp_id]
  have hpd' : p.hom ≫ d = 0 := by
    have h := congrArg (fun z => z - d) hqd
    dsimp [q] at h
    simpa [sub_comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hid : i ≫ d = 0 := by
    calc
      i ≫ d = (i ≫ e) ≫ i ≫ d := by simp [hie]
      _ = i ≫ (e ≫ i) ≫ d := by simp [Category.assoc]
      _ = 0 := by rw [hei, hpd', comp_zero]
  have hqe : q ≫ e = 0 := by
    have hpe : (e ≫ i) ≫ e = e := by simp [Category.assoc, hie]
    dsimp [q]
    rw [sub_comp, ← hei, hpe]
    simp
  have hje : j ≫ e = 0 := by
    calc
      j ≫ e = (j ≫ d) ≫ j ≫ e := by simp [hjd]
      _ = j ≫ (d ≫ j) ≫ e := by simp [Category.assoc]
      _ = 0 := by rw [hdj, hqe, comp_zero]
  have hba : a ≫ b = 𝟙 _ := by
    apply biprod.hom_ext
    · apply biprod.hom_ext'
      · simp [a, b, hie, Category.assoc]
      · simp [a, b, hje, Category.assoc]
    · apply biprod.hom_ext'
      · simp [a, b, hid, Category.assoc]
      · simp [a, b, hjd, Category.assoc]
  let eYZ : Y ⊞ Z ≅ X.obj := { hom := a, inv := b, hom_inv_id := hba, inv_hom_id := hab }
  let _ : P.IsClosedUnderIsomorphisms := hP.1
  have hYZ : P (Y ⊞ Z) := P.prop_of_iso eYZ.symm X.property
  have hY' : P.isoClosure Y := hP.2.2 (P.le_isoClosure _ hYZ) |>.1
  rw [P.isoClosure_eq_self] at hY'
  refine ⟨⟨Y, hY'⟩, ?_⟩
  refine ⟨⟨i⟩, ⟨e⟩, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    simpa only [ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom] using hie
  · apply ObjectProperty.hom_ext
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using hei

/-!
An object obtained as an arbitrary direct sum of shifts of a family `E`.
The index `0` is not singled out: an empty family is allowed, as in the
canonical zero coproduct.
-/
def IsDirectSumOfShifts {I : Type v} (E : I → C) (X : C) : Prop :=
  ∃ (J : Type v) (ι : J → I) (n : J → ℤ),
    Nonempty ((∐ fun j => (E (ι j))⟦n j⟧) ≅ X)

/-! A transition in the source's successive extension construction. -/
def IsGeneratedTransition {I : Type v} (E : I → C)
    (F : SequentialSystem C) (n : ℕ) : Prop :=
  ∃ (Y : C) (a : Y ⟶ F.obj n)
    (c : F.obj (n + 1) ⟶ Y⟦(1 : ℤ)⟧),
    IsDirectSumOfShifts E Y ∧
      Triangle.mk a (sequentialTransition F n) c ∈ distTriang C

/-!
A sequential system with the source's indexing convention: `F.obj 0` is
`X₁`, and `F.obj (n + 1)` is `Xₙ₊₂`.
-/
def IsShiftGeneratedSequence {I : Type v} (E : I → C)
    (F : SequentialSystem C) : Prop :=
  IsDirectSumOfShifts E (F.obj 0) ∧
    ∀ n : ℕ, IsGeneratedTransition E F n

section HomotopyColimitPresentation

variable [CategoryTheory.IsTriangulated C]
  [HasCountableCoproducts C]

/-!
Every object admits the source's homotopy-colimit presentation from a
compact generating family.  `IsDerivedColimit` is Chapter 33's chosen
interface for the displayed homotopy-colimit triangle.
-/
theorem exists_homotopyColimit_of_compact_generators
    {I : Type v} (E : I → C)
    (hE : ∀ i, IsCompactObject (E i))
    (hgen : IsGenerator (∐ E)) (X : C) :
    ∃ F : SequentialSystem C,
      IsDerivedColimit F X ∧ IsShiftGeneratedSequence E F := by
  sorry

end HomotopyColimitPresentation

/-!
Membership in the finitely generated subcategory used by the factorization
lemma.  The finite coproduct is the canonical finite direct sum in the
additive category, and `generatedSubcategory` is the Chapter 36 thick
subcategory generated by that finite sum.
-/
def IsInFiniteGeneratedSubcategory {I : Type v} (E : I → C) (X : C) : Prop :=
  ∃ (n : ℕ) (ι : Fin n → I),
    generatedSubcategory (∐ fun j => E (ι j)) X

/-!
Maps from a compact object into a stage of a shift-generated sequence factor
through an object generated by a finite direct sum of members of the family.
-/
theorem compact_map_factors_through_finite_generated
    {I : Type v} (E : I → C) (F : SequentialSystem C)
    (hF : IsShiftGeneratedSequence E F)
    {K : C} (hK : IsCompactObject K) {n : ℕ} (f : K ⟶ F.obj n) :
    ∃ (G : C) (g : K ⟶ G) (h : G ⟶ F.obj n),
      f = g ≫ h ∧ IsInFiniteGeneratedSubcategory E G := by
  sorry

/-! Compact generation by a set of compact objects. -/
def IsCompactlyGenerated : Prop :=
  ∃ (I : Type v) (E : I → C),
    (∀ i, IsCompactObject (E i)) ∧ IsGenerator (∐ E)

/-! Classical generation of the compact-object subcategory by one object. -/
def IsClassicalGeneratorForCompactObjects
    (E : C) : Prop :=
  compactObjects (C := C) = generatedSubcategory E

/-!
For a compact object `E`, being a classical generator of the compact
subcategory together with compact generation of the ambient category is
equivalent to being a weak generator of the ambient category.
-/
theorem generator_iff_classical_generator_for_compact_objects
    (E : C) (hE : IsCompactObject E) :
    (IsClassicalGeneratorForCompactObjects E ∧
      IsCompactlyGenerated (C := C)) ↔ IsGenerator E := by
  sorry

end CompactObjects

end Formalization.Books.Derived.Unit37
