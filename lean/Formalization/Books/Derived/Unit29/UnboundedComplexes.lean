import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Homology.Unit07.AdditiveFunctors
import Formalization.Books.Homology.Unit15.TruncationOfComplexes
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Derived Categories, Chapter 29: unbounded complexes

This file records the two canonical resolution systems used for unbounded
complexes and the criterion ensuring that a right exact functor has a left
derived functor everywhere.  The canonical complex, truncation, split-map,
quasi-isomorphism, and derived-functor interfaces are inherited from earlier
chapters and Mathlib.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Formalization.Books.Categories.Unit23
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Homology.Unit03
open Formalization.Books.Homology.Unit07
open Formalization.Books.Homology.Unit15
open scoped ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit29

/-! ## Resolution systems -/

/-- A bounded-above complex whose terms lie in the chosen class `P`. -/
def PValuedBoundedAbove {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) (K : BookComplex C) : Prop :=
  IsBoundedAbove K ∧ ∀ i : ℤ, P (K.X i)

/-- A bounded-below complex whose terms lie in the chosen class `I`. -/
def PValuedBoundedBelow {C : Type u} [Category.{v} C] [Abelian C]
    (I : ObjectProperty C) (K : BookComplex C) : Prop :=
  IsBoundedBelow K ∧ ∀ i : ℤ, I (K.X i)

/- Mathlib provides the canonical truncations and their maps to and from `K`,
   but not a named map between successive truncation objects.  These two
   minimal bridge interfaces choose the map characterized by the canonical
   factorization through `K`; their users below retain the source's actual
   truncation diagrams. -/

theorem canonicalTruncLETransition_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    ∃ f : CochainComplex.canonicalTruncLE K ((n : ℤ) + 1) ⟶
        CochainComplex.canonicalTruncLE K ((n : ℤ) + 2),
      f ≫ CochainComplex.canonicalTruncLEι K ((n : ℤ) + 2) =
        CochainComplex.canonicalTruncLEι K ((n : ℤ) + 1) := by
  have hLow : (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).IsStrictlyLE
      ((n : ℤ) + 1) := by
    dsimp [CochainComplex.canonicalTruncLE]
    infer_instance
  have hHigh : (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).IsStrictlyLE
      ((n : ℤ) + 2) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.isStrictlyLE_iff
      (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)) ((n : ℤ) + 1)).1 hLow i (by omega)
  have hs : IsIso ((CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).ιTruncLE
      ((n : ℤ) + 2)) :=
    (CochainComplex.isIso_ιTruncLE_iff _ _).2 hHigh
  let i : (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).truncLE ((n : ℤ) + 2) ≅
      CochainComplex.canonicalTruncLE K ((n : ℤ) + 1) :=
    { hom := (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).ιTruncLE ((n : ℤ) + 2)
      inv := Classical.choose hs.out
      hom_inv_id := (Classical.choose_spec hs.out).1
      inv_hom_id := (Classical.choose_spec hs.out).2 }
  let g : (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).truncLE ((n : ℤ) + 2) ⟶
      CochainComplex.canonicalTruncLE K ((n : ℤ) + 2) := by
    change (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).truncLE ((n : ℤ) + 2) ⟶
      CochainComplex.truncLE K ((n : ℤ) + 2)
    exact CochainComplex.truncLEMap (CochainComplex.canonicalTruncLEι K ((n : ℤ) + 1))
      ((n : ℤ) + 2)
  have hg : g ≫ CochainComplex.canonicalTruncLEι K ((n : ℤ) + 2) =
      (CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)).ιTruncLE ((n : ℤ) + 2) ≫
        CochainComplex.canonicalTruncLEι K ((n : ℤ) + 1) := by
    dsimp [g, CochainComplex.canonicalTruncLEι, CochainComplex.canonicalTruncLE]
    exact CochainComplex.ιTruncLE_naturality _ _
  exact ⟨i.inv ≫ g, by rw [Category.assoc, hg, i.inv_hom_id_assoc]⟩

noncomputable def canonicalTruncLETransition
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    CochainComplex.canonicalTruncLE K ((n : ℤ) + 1) ⟶
      CochainComplex.canonicalTruncLE K ((n : ℤ) + 2) :=
  Classical.choose (canonicalTruncLETransition_exists K n)

theorem canonicalTruncLETransition_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    canonicalTruncLETransition K n ≫
        CochainComplex.canonicalTruncLEι K ((n : ℤ) + 2) =
      CochainComplex.canonicalTruncLEι K ((n : ℤ) + 1) :=
  Classical.choose_spec (canonicalTruncLETransition_exists K n)

theorem canonicalTruncGETransition_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    ∃ f : CochainComplex.canonicalTruncGE K (-((n : ℤ) + 2)) ⟶
        CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1)),
      CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 2)) ≫ f =
        CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 1)) := by
  let low : ℤ := -((n : ℤ) + 2)
  let high : ℤ := -((n : ℤ) + 1)
  have hHigh : (CochainComplex.canonicalTruncGE K high).IsStrictlyGE high := by
    dsimp [high, CochainComplex.canonicalTruncGE]
    infer_instance
  have hLow : (CochainComplex.canonicalTruncGE K high).IsStrictlyGE low := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (CochainComplex.isStrictlyGE_iff
      (CochainComplex.canonicalTruncGE K high) high).1 hHigh i (by omega)
  have hs : IsIso ((CochainComplex.canonicalTruncGE K high).πTruncGE low) :=
    (CochainComplex.isIso_πTruncGE_iff _ _).2 hLow
  let i : CochainComplex.canonicalTruncGE K high ≅
      (CochainComplex.canonicalTruncGE K high).truncGE low :=
    { hom := (CochainComplex.canonicalTruncGE K high).πTruncGE low
      inv := Classical.choose hs.out
      hom_inv_id := (Classical.choose_spec hs.out).1
      inv_hom_id := (Classical.choose_spec hs.out).2 }
  let g : CochainComplex.canonicalTruncGE K low ⟶
      (CochainComplex.canonicalTruncGE K high).truncGE low := by
    change CochainComplex.truncGE K low ⟶ (CochainComplex.truncGE K high).truncGE low
    exact CochainComplex.truncGEMap (CochainComplex.canonicalTruncGEπ K high) low
  have hg : CochainComplex.canonicalTruncGEπ K low ≫ g =
      CochainComplex.canonicalTruncGEπ K high ≫
        (CochainComplex.canonicalTruncGE K high).πTruncGE low := by
    dsimp [g]
    exact CochainComplex.πTruncGE_naturality _ _
  refine ⟨g ≫ i.inv, ?_⟩
  rw [← Category.assoc, hg]
  change (CochainComplex.canonicalTruncGEπ K high ≫ i.hom) ≫ i.inv =
    CochainComplex.canonicalTruncGEπ K high
  simp

noncomputable def canonicalTruncGETransition
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    CochainComplex.canonicalTruncGE K (-((n : ℤ) + 2)) ⟶
      CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1)) :=
  Classical.choose (canonicalTruncGETransition_exists K n)

theorem canonicalTruncGETransition_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) [∀ i : ℤ, K.HasHomology i] (n : ℕ) :
    CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 2)) ≫
        canonicalTruncGETransition K n =
      CochainComplex.canonicalTruncGEπ K (-((n : ℤ) + 1)) :=
  Classical.choose_spec (canonicalTruncGETransition_exists K n)

/--
The commutative diagram of bounded-above `P`-valued replacements of the
canonical truncations `τ ≤ n K`.

The index `n` represents the source's `P_{n+1}` and `τ ≤ (n+1) K`.
-/
structure SpecialDirectSystem
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C) (K : BookComplex C)
    [∀ i : ℤ, K.HasHomology i] where
  stage : ℕ → BookComplex C
  transition : ∀ n : ℕ, stage n ⟶ stage (n + 1)
  comparison : ∀ n : ℕ,
    stage n ⟶ CochainComplex.canonicalTruncLE K ((n : ℤ) + 1)
  comm : ∀ n : ℕ,
    transition n ≫ comparison (n + 1) =
      comparison n ≫ canonicalTruncLETransition K n
  quasiIso : ∀ n : ℕ, QuasiIsomorphism (comparison n)
  termwiseEpi : ∀ (n : ℕ) (i : ℤ), Epi ((comparison n).f i)
  bounded : ∀ n : ℕ, PValuedBoundedAbove P (stage n)
  splitMono : ∀ n : ℕ,
    Formalization.Books.Derived.Unit09.termwiseSplitInjection (transition n)
  cokernel_mem : ∀ (n : ℕ) (i : ℤ),
    P (cokernel ((transition n).f i))

/- The source's first numbered result: existence of the direct resolution
   system with all three displayed properties. -/
theorem specialDirectSystem_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : ObjectProperty C)
    (hP0 : P (0 : C))
    (hPsum : ∀ X Y : C, P X → P Y → P (X ⊞ Y))
    (hPquot : ∀ X : C, ∃ Y : C, P Y ∧ ∃ f : Y ⟶ X, Epi f)
    (K : BookComplex C) :
    Nonempty (SpecialDirectSystem P K) := by
  sorry

/-! ## Existence of the left derived functor -/

/-- The complex functor induced by a right exact functor. -/
noncomputable def mapComplexOfRightExact
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) (hF : IsRightExact F) :
    BookComplex A ⥤ BookComplex B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inr hF)
  exact F.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The homotopy-category functor induced by a right exact functor. -/
noncomputable def mapHomotopyOfRightExact
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (F : A ⥤ B) (hF : IsRightExact F) :
    BookHomotopyCategory A ⥤ BookHomotopyCategory B := by
  letI : F.Additive := left_or_right_exact_additive F (Or.inr hF)
  exact F.mapHomotopyCategory (ComplexShape.up ℤ)

/- The source's second numbered result.  The four bracketed categorical
   assumptions are the hypotheses that the relevant sequential colimits
   exist and are exact in both abelian categories, and that `F` preserves
   them. -/
theorem leftDerived_exists_of_specialDirectSystem
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) (hF : IsRightExact F)
    [PreservesColimitsOfShape ℕ F]
    (P : ObjectProperty A)
    (hP0 : P (0 : A))
    (hPsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hPquot : ∀ X : A, ∃ Y : A, P Y ∧ ∃ f : Y ⟶ X, Epi f)
    (hFacyclic :
      ∀ K : BookComplex A,
        PValuedBoundedAbove P K →
          AcyclicComplex K →
            AcyclicComplex ((mapComplexOfRightExact F hF).obj K)) :
    LeftDerivable
      (quasiIsoHomotopyProperty A)
      (quasiIsoHomotopyProperty_properties A).1
      (mapHomotopyOfRightExact F hF) := by
  sorry

/-! ## The dual inverse system -/

/--
The commutative diagram of bounded-below `I`-valued replacements of the
canonical truncations `τ ≥ -n K`.

The index `n` represents the source's `I_{n+1}` and `τ ≥ -(n+1) K`.
-/
structure SpecialInverseSystem
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : ObjectProperty C) (K : BookComplex C)
    [∀ i : ℤ, K.HasHomology i] where
  stage : ℕ → BookComplex C
  transition : ∀ n : ℕ, stage (n + 1) ⟶ stage n
  comparison : ∀ n : ℕ,
    CochainComplex.canonicalTruncGE K (-((n : ℤ) + 1)) ⟶ stage n
  comm : ∀ n : ℕ,
    canonicalTruncGETransition K n ≫ comparison n =
      comparison (n + 1) ≫ transition n
  quasiIso : ∀ n : ℕ, QuasiIsomorphism (comparison n)
  termwiseMono : ∀ (n : ℕ) (i : ℤ), Mono ((comparison n).f i)
  bounded : ∀ n : ℕ, PValuedBoundedBelow I (stage n)
  splitEpi : ∀ n : ℕ,
    Formalization.Books.Derived.Unit09.termwiseSplitSurjection (transition n)
  kernel_mem : ∀ (n : ℕ) (i : ℤ),
    I (kernel ((transition n).f i))

/- The source's third numbered result, dual to the direct-system result. -/
theorem specialInverseSystem_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (I : ObjectProperty C)
    (hI0 : I (0 : C))
    (hIprod : ∀ X Y : C, I X → I Y → I (X ⨯ Y))
    (hIsub : ∀ X : C, ∃ Y : C, I Y ∧ ∃ f : X ⟶ Y, Mono f)
    (K : BookComplex C) :
    Nonempty (SpecialInverseSystem I K) := by
  sorry

end Formalization.Books.Derived.Unit29
