import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ExactSequence
import Formalization.Books.Derived.Unit11.DerivedCategories
import Formalization.Books.Derived.Unit18.InjectiveResolutions
import Formalization.Books.Derived.Unit19.ProjectiveResolutions
import Formalization.Books.Homology.Unit06.Extensions

/-!
# Derived Categories, Chapter 27: Ext groups

The chapter's Ext groups are shifted Hom groups in the derived category.  This
file records the integer-graded interface, the exact windows coming from
triangles, resolution computations, Yoneda extensions, and the splitting
criterion at the end of the chapter.  Proofs of the substantive comparison
and classification statements are intentionally deferred.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit18
open Formalization.Books.Derived.Unit19
open Formalization.Books.Homology.Unit06
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit27

/-! ## Definition and functoriality -/

/-- The book's integer-graded derived Ext group.

The first displayed presentation in the source is used as the definition;
the opposite-shift presentation is recorded by
`derivedExt_shift_presentation` below.
-/
abbrev DerivedExt
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X Y : DerivedCategory C) (i : ℤ) : Type _ :=
  ShiftedHom X Y i

/-- The derived object associated to an object of the heart. -/
abbrev DerivedObject
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (A : C) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C 0).obj A

/-- `Ext` for objects of the abelian heart, with the book's argument order. -/
abbrev ObjectDerivedExt
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (B A : C) (i : ℤ) : Type _ :=
  DerivedExt (DerivedObject B) (DerivedObject A) i

/-- A source-facing predicate for a derived Ext group to vanish. -/
def DerivedExtVanishes
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X Y : DerivedCategory C) (i : ℤ) : Prop :=
  ∀ ξ : DerivedExt X Y i, ξ = 0

/-- The integer-shift version of the second presentation of Ext. -/
theorem derivedExt_shift_presentation
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X Y : DerivedCategory C) (i : ℤ) :
    Nonempty
      (DerivedExt X Y i ≃+
        ((shiftFunctor (DerivedCategory C) (-i)).obj X ⟶ Y)) := by
  sorry

/-- Composition of an `i`-extension with a `j`-extension.

The first argument is the class on the right in the book's notation, so the
result is the usual `η ∘ ξ` with `ξ` applied first.
-/
noncomputable def derivedExtComp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} {i j k : ℤ}
    (η : DerivedExt Y Z j) (ξ : DerivedExt X Y i) (h : j + i = k) :
    DerivedExt X Z k :=
  ShiftedHom.comp ξ η h

theorem derivedExtComp_add_right
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} {i j k : ℤ}
    (η : DerivedExt Y Z j) (ξ₁ ξ₂ : DerivedExt X Y i) (h : j + i = k) :
    derivedExtComp η (ξ₁ + ξ₂) h =
      derivedExtComp η ξ₁ h + derivedExtComp η ξ₂ h := by
  sorry

theorem derivedExtComp_add_left
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} {i j k : ℤ}
    (η₁ η₂ : DerivedExt Y Z j) (ξ : DerivedExt X Y i) (h : j + i = k) :
    derivedExtComp (η₁ + η₂) ξ h =
      derivedExtComp η₁ ξ h + derivedExtComp η₂ ξ h := by
  sorry

theorem derivedExtComp_assoc
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {W X Y Z : DerivedCategory C} {a b c k m l : ℤ}
    (θ : DerivedExt Z W c) (η : DerivedExt Y Z b) (ξ : DerivedExt X Y a)
    (h₁ : b + a = k) (h₂ : c + k = l)
    (h₃ : c + b = m) (h₄ : m + a = l) :
    derivedExtComp θ (derivedExtComp η ξ h₁) h₂ =
      derivedExtComp (derivedExtComp θ η h₃) ξ h₄ := by
  sorry

/-! ## Exact windows and full subcategories -/

/-- Postcomposition by a degree-zero morphism on a shifted Hom group. -/
noncomputable def derivedExtPostcomp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} (f : Y ⟶ Z) (i : ℤ) :
    DerivedExt X Y i →+ DerivedExt X Z i where
  toFun ξ := derivedExtComp (ShiftedHom.mk₀ (0 : ℤ) rfl f) ξ (by simp)
  map_zero' := by simp [derivedExtComp]
  map_add' ξ₁ ξ₂ := by simp [derivedExtComp]

/-- Postcomposition by the connecting morphism of a triangle. -/
noncomputable def derivedExtPostcompShift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} (f : Y ⟶ Z⟦(1 : ℤ)⟧) (i : ℤ) :
    DerivedExt X Y i →+ DerivedExt X Z (i + 1) where
  toFun ξ := derivedExtComp f ξ (by simp [add_comm])
  map_zero' := by simp [derivedExtComp]
  map_add' ξ₁ ξ₂ := by simp [derivedExtComp]

/-- Precomposition by a degree-zero morphism on a shifted Hom group. -/
noncomputable def derivedExtPrecomp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} (f : X ⟶ Y) (i : ℤ) :
    DerivedExt Y Z i →+ DerivedExt X Z i where
  toFun η := derivedExtComp η (ShiftedHom.mk₀ (0 : ℤ) rfl f) (by simp)
  map_zero' := by simp [derivedExtComp]
  map_add' η₁ η₂ := by simp [derivedExtComp]

/-- Precomposition by a degree-one morphism on a shifted Hom group. -/
noncomputable def derivedExtPrecompShift
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {X Y Z : DerivedCategory C} (f : X ⟶ Y⟦(1 : ℤ)⟧) (i : ℤ) :
    DerivedExt Y Z i →+ DerivedExt X Z (i + 1) where
  toFun η := derivedExtComp η f (by rfl)
  map_zero' := by simp [derivedExtComp]
  map_add' η₁ η₂ := by simp [derivedExtComp]

/-- The five-arrow covariant exact window attached to a distinguished triangle. -/
noncomputable def derivedExtCovariantWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T : Triangle (DerivedCategory C)) (X : DerivedCategory C) (i : ℤ) :
    ComposableArrows AddCommGrpCat 5 :=
  ComposableArrows.mk₅
    (AddCommGrpCat.ofHom (derivedExtPostcomp (X := X) T.mor₁ i))
    (AddCommGrpCat.ofHom (derivedExtPostcomp (X := X) T.mor₂ i))
    (AddCommGrpCat.ofHom (derivedExtPostcompShift (X := X) T.mor₃ i))
    (AddCommGrpCat.ofHom (derivedExtPostcomp (X := X) T.mor₁ (i + 1)))
    (AddCommGrpCat.ofHom (derivedExtPostcomp (X := X) T.mor₂ (i + 1)))

/-- The five-arrow contravariant exact window attached to a distinguished triangle. -/
noncomputable def derivedExtContravariantWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T : Triangle (DerivedCategory C)) (Y : DerivedCategory C) (i : ℤ) :
    ComposableArrows AddCommGrpCat 5 :=
  ComposableArrows.mk₅
    (AddCommGrpCat.ofHom (derivedExtPrecomp (Z := Y) T.mor₂ i))
    (AddCommGrpCat.ofHom (derivedExtPrecomp (Z := Y) T.mor₁ i))
    (AddCommGrpCat.ofHom (derivedExtPrecompShift (Z := Y) T.mor₃ i))
    (AddCommGrpCat.ofHom (derivedExtPrecomp (Z := Y) T.mor₂ (i + 1)))
    (AddCommGrpCat.ofHom (derivedExtPrecomp (Z := Y) T.mor₁ (i + 1)))

theorem derivedExtCovariantWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
    (X : DerivedCategory C) (i : ℤ) :
    (derivedExtCovariantWindow T X i).Exact := by
  sorry

theorem derivedExtContravariantWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C))
    (Y : DerivedCategory C) (i : ℤ) :
    (derivedExtContravariantWindow T Y i).Exact := by
  sorry

/- The short-exact case is the source's six-term long exact sequence starting
at degree zero; Mathlib supplies the distinguished triangle `singleTriangle`. -/
noncomputable def shortExactDerivedExtCovariantWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : DerivedCategory C) (i : ℤ) :
    ComposableArrows AddCommGrpCat 5 :=
  derivedExtCovariantWindow hS.singleTriangle X i

noncomputable def shortExactDerivedExtContravariantWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : DerivedCategory C) (i : ℤ) :
    ComposableArrows AddCommGrpCat 5 :=
  derivedExtContravariantWindow hS.singleTriangle Y i

/-- The initial covariant window, including the leading zero in the source. -/
noncomputable def shortExactDerivedExtCovariantInitialWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : DerivedCategory C) :
    ComposableArrows AddCommGrpCat 6 :=
  (shortExactDerivedExtCovariantWindow hS X 0).precomp
    (0 : (0 : AddCommGrpCat) ⟶
      (shortExactDerivedExtCovariantWindow hS X 0).left)

/-- The initial contravariant window, including the leading zero in the source. -/
noncomputable def shortExactDerivedExtContravariantInitialWindow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : DerivedCategory C) :
    ComposableArrows AddCommGrpCat 6 :=
  (shortExactDerivedExtContravariantWindow hS Y 0).precomp
    (0 : (0 : AddCommGrpCat) ⟶
      (shortExactDerivedExtContravariantWindow hS Y 0).left)

theorem shortExactDerivedExtCovariantWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : DerivedCategory C) (i : ℤ) :
    (shortExactDerivedExtCovariantWindow hS X i).Exact := by
  sorry

theorem shortExactDerivedExtContravariantWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : DerivedCategory C) (i : ℤ) :
    (shortExactDerivedExtContravariantWindow hS Y i).Exact := by
  sorry

theorem shortExactDerivedExtCovariantInitialWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (X : DerivedCategory C) :
    (shortExactDerivedExtCovariantInitialWindow hS X).Exact := by
  sorry

theorem shortExactDerivedExtContravariantInitialWindow_exact
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) (Y : DerivedCategory C) :
    (shortExactDerivedExtContravariantInitialWindow hS Y).Exact := by
  sorry

/-- A full, faithful, shift-compatible functor preserves the book's shifted Hom groups. -/
theorem fullFaithful_shiftedHom_bijective
    {C : Type u} {D : Type v} [Category.{u} C] [Category.{v} D]
    [HasShift C ℤ] [HasShift D ℤ]
    (F : C ⥤ D) [F.Full] [F.Faithful] [F.CommShift ℤ]
    (X Y : C) (i : ℤ) :
    Function.Bijective
      (fun f : ShiftedHom X Y i => ShiftedHom.map f F) := by
  sorry

/-! ## Resolution computations -/

abbrev DerivedComplexObject
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : BookComplex C) : DerivedCategory C :=
  (DerivedCategory.Qh (C := C)).obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)

abbrev HomotopyComplexObject
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : BookComplex C) : BookHomotopyCategory C :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K

abbrev DerivedComplexExt
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : BookComplex C) (i : ℤ) : Type _ :=
  DerivedExt (DerivedComplexObject K) (DerivedComplexObject L) i

theorem derivedExt_compute_by_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : BookComplex C) (R : ComplexInjectiveResolution L) (i : ℤ) :
    Nonempty
      (DerivedComplexExt K L i ≃+
        ShiftedHom (HomotopyComplexObject K)
          (HomotopyComplexObject R.target) i) := by
  sorry

theorem derivedExt_compute_by_projective_resolution
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : BookComplex C) (R : ComplexProjectiveResolution K) (i : ℤ) :
    Nonempty
      (DerivedComplexExt K L i ≃+
        ((shiftFunctor (BookHomotopyCategory C) (-i)).obj
            (HomotopyComplexObject R.source) ⟶ HomotopyComplexObject L)) := by
  sorry

/-! ## Cohomological bounds and negative Ext -/

def DerivedCohomologyVanishesAbove
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) (a : ℤ) : Prop :=
  ∀ n : ℤ, a < n → IsZero ((derivedCohomologyFunctor C n).obj X)

def DerivedCohomologyVanishesBelow
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (Y : DerivedCategory C) (b : ℤ) : Prop :=
  ∀ n : ℤ, n < b → IsZero ((derivedCohomologyFunctor C n).obj Y)

theorem derivedExt_vanishes_below_cohomological_gap
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X Y : DerivedCategory C) (a b : ℤ)
    (hX : DerivedCohomologyVanishesAbove X a)
    (hY : DerivedCohomologyVanishesBelow Y b) :
    (∀ n : ℤ, n < b - a → DerivedExtVanishes X Y n) ∧
      Nonempty
        (DerivedExt X Y (b - a) ≃+
          ((derivedCohomologyFunctor C a).obj X ⟶
            (derivedCohomologyFunctor C b).obj Y)) := by
  sorry

theorem objectDerivedExt_vanishes_for_negative_degree
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B : C) {i : ℤ} (hi : i < 0) :
    DerivedExtVanishes (DerivedObject B) (DerivedObject A) i := by
  sorry

theorem objectDerivedExt_zero_is_hom
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B : C) :
    Nonempty (ObjectDerivedExt B A 0 ≃+ (B ⟶ A)) := by
  sorry

/-! The canonical degree-one class of a short exact sequence is used by the
iterated Yoneda splice below. -/

/-- The canonical derived class of a short exact sequence. -/
noncomputable def shortExactDerivedExtClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    ObjectDerivedExt S.X₃ S.X₁ 1 :=
  hS.singleδ

/-! ## Yoneda extensions -/

/-- A literal finite exact sequence presentation of a degree-`i` extension.

The middle objects occur at indices `2` through `i + 1`; this keeps the
source's `0 → A → Z_{i-1} → ⋯ → Z₀ → B → 0` diagram visible in Lean.
-/
structure YonedaExtensionSequence
    (C : Type u) [Category.{v} C] [Abelian C]
    (A B : C) (i : ℕ) (hi : 1 ≤ i) where
  sequence : ComposableArrows C (i + 3)
  leftZero : sequence.obj' 0 = 0
  leftObject : sequence.obj' 1 = A
  rightObject : sequence.obj' (i + 2) = B
  rightZero : sequence.obj' (i + 3) = 0
  exact : sequence.Exact

/-- The `j`th middle object of a literal Yoneda extension sequence. -/
def yonedaExtensionMiddle
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) (j : Fin i) : C :=
  E.sequence.obj' (j.val + 2)

/-- A commutative diagram of finite Yoneda extension sequences. -/
structure YonedaExtensionDiagramHom
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E F : YonedaExtensionSequence C A B i hi) where
  map : E.sequence ⟶ F.sequence
  atLeftZero : map.app 0 =
    eqToHom E.leftZero ≫ eqToHom F.leftZero.symm
  atLeftObject : map.app 1 =
    eqToHom E.leftObject ≫ eqToHom F.leftObject.symm
  atRightObject : map.app ⟨i + 2, by omega⟩ =
    eqToHom E.rightObject ≫ eqToHom F.rightObject.symm
  atRightZero : map.app ⟨i + 3, by omega⟩ =
    eqToHom E.rightZero ≫ eqToHom F.rightZero.symm

/-- The source's common-middle-object equivalence relation on Yoneda extensions. -/
def YonedaExtensionEquivalent
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E F : YonedaExtensionSequence C A B i hi) : Prop :=
  ∃ G : YonedaExtensionSequence C A B i hi,
    Nonempty (YonedaExtensionDiagramHom G E) ∧
      Nonempty (YonedaExtensionDiagramHom G F)

theorem yonedaExtensionEquivalent_refl
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) :
    YonedaExtensionEquivalent E E := by
  sorry

theorem yonedaExtensionEquivalent_symm
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    {E F : YonedaExtensionSequence C A B i hi} :
    YonedaExtensionEquivalent E F → YonedaExtensionEquivalent F E := by
  sorry

theorem yonedaExtensionEquivalent_trans
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    {E F G : YonedaExtensionSequence C A B i hi} :
    YonedaExtensionEquivalent E F → YonedaExtensionEquivalent F G →
      YonedaExtensionEquivalent E G := by
  sorry

/- The iterated-short-exact presentation is the computational Yoneda model:
each `cons` splices one short exact extension onto a shorter one. -/
inductive YonedaSplice
    (C : Type u) [Category.{v} C] [Abelian C] :
    C → C → ℕ → Type (max u v)
  | one {A B : C}
      (E : Formalization.Books.Homology.Unit06.Extension C A B) :
      YonedaSplice C A B 1
  | cons {A M B : C}
      (E : Formalization.Books.Homology.Unit06.Extension C A M)
      {n : ℕ} (tail : YonedaSplice C M B n) :
      YonedaSplice C A B (n + 1)

abbrev YonedaExtension := YonedaSplice

/-- The derived Ext class of an extension represented by an iterated splice. -/
noncomputable def yonedaSpliceClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {n : ℕ} :
    YonedaSplice C A B n → ObjectDerivedExt B A (n : ℤ)
  | @YonedaSplice.one _ _ _ A B E => shortExactDerivedExtClass E.shortExact
  | @YonedaSplice.cons _ _ _ A M B E n tail =>
      derivedExtComp
        (shortExactDerivedExtClass E.shortExact)
        (@yonedaSpliceClass C _ _ _ M B n tail) (by omega)

theorem yonedaSpliceClass_cons
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B M : C} {n : ℕ}
    (E : Formalization.Books.Homology.Unit06.Extension C A M)
    (tail : YonedaSplice C M B n) :
    yonedaSpliceClass (.cons E tail) =
      derivedExtComp
        (shortExactDerivedExtClass E.shortExact)
        (@yonedaSpliceClass C _ _ _ M B n tail) (by omega) := by
  rfl

/-- A complex-level representative of the two maps used in the source's
definition of `δ(E)`. -/
structure YonedaComplexWitness
    (C : Type u) [Category.{v} C] [Abelian C]
    (A B : C) (i : ℕ) where
  complex : BookComplex C
  s : complex ⟶ (CochainComplex.singleFunctor C 0).obj B
  quasiIso : QuasiIso s
  f : complex ⟶
    (shiftFunctor (BookComplex C) (i : ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj A)

/-- The derived representative `f s⁻¹` used by the source's Yoneda class. -/
structure YonedaDerivedWitness
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) where
  source : DerivedCategory C
  s : source ⟶ DerivedObject B
  f : ShiftedHom source (DerivedObject A) (i : ℤ)
  s_isIso : IsIso s
  complexWitness : YonedaComplexWitness C A B i
  presentation : YonedaExtensionSequence C A B i hi
  presentation_equivalent : YonedaExtensionEquivalent E presentation

noncomputable def yonedaDerivedWitnessClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    {E : YonedaExtensionSequence C A B i hi}
    (W : YonedaDerivedWitness C E) : ObjectDerivedExt B A (i : ℤ) := by
  letI := W.s_isIso
  exact derivedExtComp W.f (ShiftedHom.mk₀ (0 : ℤ) rfl (inv W.s)) (by simp)

/-- Being the class induced by a particular Yoneda extension. -/
def IsYonedaExtensionClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi)
    (ξ : ObjectDerivedExt B A (i : ℤ)) : Prop :=
  ∃ W : YonedaDerivedWitness C E, ξ = yonedaDerivedWitnessClass W

theorem yonedaExtensionClass_exists
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) :
    ∃ ξ : ObjectDerivedExt B A (i : ℤ), IsYonedaExtensionClass E ξ := by
  sorry

/-- A chosen derived class for a finite Yoneda extension sequence. -/
noncomputable def yonedaExtensionClass
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) :
    ObjectDerivedExt B A (i : ℤ) :=
  Classical.choose (yonedaExtensionClass_exists E)

theorem yonedaExtensionClass_is_induced
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E : YonedaExtensionSequence C A B i hi) :
    IsYonedaExtensionClass E (yonedaExtensionClass E) :=
  Classical.choose_spec (yonedaExtensionClass_exists E)

theorem yoneda_extension_classification
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B : C} {i : ℕ} {hi : 1 ≤ i}
    (E F : YonedaExtensionSequence C A B i hi) :
    YonedaExtensionEquivalent E F ↔
      yonedaExtensionClass E = yonedaExtensionClass F := by
  sorry

theorem yoneda_extension_surjective
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B : C) {i : ℕ} (hi : 1 ≤ i) :
    ∀ ξ : ObjectDerivedExt B A (i : ℤ),
      ∃ E : YonedaExtensionSequence C A B i hi,
        yonedaExtensionClass E = ξ := by
  sorry

theorem yoneda_splicing_represents_derivedExtComp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B C' : C} {i j : ℕ}
    (E : YonedaSplice C A B i) (F : YonedaSplice C B C' j) :
    ∃ G : YonedaSplice C A C' (i + j),
      yonedaSpliceClass G =
        derivedExtComp (yonedaSpliceClass E) (yonedaSpliceClass F) (by omega) := by
  sorry

/-! ## Degree one and the cup product -/

theorem derivedExt_one_agrees_with_homology_Ext
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (A B : C) :
    Nonempty
      (ObjectDerivedExt B A 1 ≃+
        Formalization.Books.Homology.Unit06.Ext B A) := by
  sorry

/-- The product of two degree-one short-exact extension classes. -/
noncomputable def shortExactDerivedExtCup
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B C' : C}
    (top : Formalization.Books.Homology.Unit06.Extension C A B)
    (bottom : Formalization.Books.Homology.Unit06.Extension C B C') :
    ObjectDerivedExt C' A 2 :=
  derivedExtComp (shortExactDerivedExtClass top.shortExact)
    (shortExactDerivedExtClass bottom.shortExact) (by simp)

/-- The diagram supplied by the vanishing cup-product criterion.

The two rows and the two nontrivial middle/right columns are represented by
Mathlib short complexes; the missing outer columns are the identity columns.
-/
structure CupExtLadder
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B C' : C}
    (top : Formalization.Books.Homology.Unit06.Extension C A B)
    (bottom : Formalization.Books.Homology.Unit06.Extension C B C') where
  W : C
  aW : A ⟶ W
  zW : top.middle ⟶ W
  bZ' : B ⟶ bottom.middle
  wZ' : W ⟶ bottom.middle
  z'C' : bottom.middle ⟶ C'
  wC' : W ⟶ C'
  bottomZero : aW ≫ wZ' = 0
  middleZero : zW ≫ wC' = 0
  rightZero : bZ' ≫ z'C' = 0
  bottomExact : (ShortComplex.mk aW wZ' bottomZero).ShortExact
  middleExact : (ShortComplex.mk zW wC' middleZero).Exact
  rightExact : (ShortComplex.mk bZ' z'C' rightZero).Exact
  commA : top.inclusion ≫ zW = aW
  commB : zW ≫ wZ' = top.projection ≫ bZ'
  commC : wZ' ≫ z'C' = wC'

theorem shortExactDerivedExtCup_eq_zero_iff
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {A B C' : C}
    (top : Formalization.Books.Homology.Unit06.Extension C A B)
    (bottom : Formalization.Books.Homology.Unit06.Extension C B C') :
    shortExactDerivedExtCup top bottom = 0 ↔
    Nonempty (CupExtLadder top bottom) := by
  sorry

/-! ## Higher vanishing and splitting -/

theorem higher_object_ext_vanishes
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (p : ℕ)
    (h : ∀ A B : C,
      DerivedExtVanishes (DerivedObject B) (DerivedObject A) (p : ℤ)) :
    ∀ n : ℕ, p ≤ n → ∀ A B : C,
      DerivedExtVanishes (DerivedObject B) (DerivedObject A) (n : ℤ) := by
  sorry

def BoundedCohomologySupported
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DBounded C) (a : ℤ) (n : ℕ) : Prop :=
  ∀ i : ℤ, (i < a ∨ a + (n : ℤ) < i) →
    IsZero
      ((derivedCohomologyFunctor C i).obj
        ((DerivedCategory.Bounded.ι (C := C)).obj K))

/- The finite index form is the literal meaning of the book's displayed
direct sum: an object of `Dᵇ` has only finitely many nonzero cohomologies. -/
noncomputable def finiteCohomologyDirectSum
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DBounded C) (a : ℤ) (n : ℕ) : DerivedCategory C :=
  ⨁ fun j : Fin (n + 1) =>
    (shiftFunctor (DerivedCategory C) (-(a + (j : ℤ)))).obj
      ((DerivedCategory.singleFunctor C 0).obj
        ((derivedCohomologyFunctor C (a + (j : ℤ))).obj
          ((DerivedCategory.Bounded.ι (C := C)).obj K)))

theorem derivedBounded_formal_decomposition
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DBounded C)
    (hExt : ∀ p : ℕ, 2 ≤ p → ∀ A B : C,
      DerivedExtVanishes (DerivedObject B) (DerivedObject A) (p : ℤ)) :
    ∃ a : ℤ, ∃ n : ℕ,
      BoundedCohomologySupported K a n ∧
        Nonempty
          (((DerivedCategory.Bounded.ι (C := C)).obj K) ≅
            finiteCohomologyDirectSum K a n) := by
  sorry

theorem derivedBounded_formal_decomposition_of_ext_two
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DBounded C)
    (hExt : ∀ A B : C,
      DerivedExtVanishes (DerivedObject B) (DerivedObject A) 2) :
    ∃ a : ℤ, ∃ n : ℕ,
      BoundedCohomologySupported K a n ∧
        Nonempty
          (((DerivedCategory.Bounded.ι (C := C)).obj K) ≅
            finiteCohomologyDirectSum K a n) := by
  sorry

end Formalization.Books.Derived.Unit27
