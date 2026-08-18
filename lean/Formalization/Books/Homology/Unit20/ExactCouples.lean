import Formalization.Books.Homology.Unit20.SpectralSequences
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Spectral sequences from exact couples

This file keeps exactness in Mathlib's `ShortComplex.Exact` interface.  The
derived couple is presented on the actual image and homology objects; the
existence theorem is left for the proof stage because the induced maps are
universal-property constructions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.2 Spectral sequences: exact couples -/

/-- An exact couple in an abelian category, with its three cyclic exactness
conditions written as exact short complexes. -/
structure ExactCouple (C : Type u) [Category.{v} C] [Abelian C]
    (A E : C) where
  alpha : A ⟶ A
  f : E ⟶ A
  g : A ⟶ E
  alpha_g : alpha ≫ g = 0
  g_f : g ≫ f = 0
  f_alpha : f ≫ alpha = 0
  exact_alpha_g : (ShortComplex.mk alpha g alpha_g).Exact
  exact_g_f : (ShortComplex.mk g f g_f).Exact
  exact_f_alpha : (ShortComplex.mk f alpha f_alpha).Exact

/-- A morphism of exact couples. -/
structure ExactCoupleHom {C : Type u} [Category.{v} C] [Abelian C]
    {A E A' E' : C} (D : ExactCouple C A E) (D' : ExactCouple C A' E') where
  tA : A ⟶ A'
  tE : E ⟶ E'
  alpha_comm : tA ≫ D'.alpha = D.alpha ≫ tA
  f_comm : tE ≫ D'.f = D.f ≫ tA
  g_comm : tA ≫ D'.g = D.g ≫ tE

/-- The first differential produced by an exact couple. -/
def exactCoupleDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : E ⟶ E := D.f ≫ D.g

theorem exactCoupleDifferential_sq {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    exactCoupleDifferential D ≫ exactCoupleDifferential D = 0 := by
  sorry

/-- The homology object of the differential of an exact couple. -/
abbrev exactCoupleDerivedE {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : C :=
  differentialHomology (exactCoupleDifferential D) (exactCoupleDifferential_sq D)

noncomputable def exactCoupleDerivedBoundaryMap {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    Abelian.image (exactCoupleDifferential D) ⟶
      kernel (exactCoupleDifferential D) :=
  kernel.lift (exactCoupleDifferential D)
    (Abelian.image.ι (exactCoupleDifferential D))
    (Abelian.image_ι_comp_eq_zero (exactCoupleDifferential_sq D))

/-- The image object which is the next `A`-term of a derived exact couple. -/
abbrev exactCoupleDerivedA {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : C := Abelian.image D.alpha

/-- The induced maps are retained as part of the derived-couple interface. -/
structure ExactCoupleDerivedData {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) where
  couple : ExactCouple C (exactCoupleDerivedA D) (exactCoupleDerivedE D)
  alpha_spec : couple.alpha ≫ Abelian.image.ι D.alpha =
    Abelian.image.ι D.alpha ≫ D.alpha
  f_cycle : kernel (exactCoupleDifferential D) ⟶ exactCoupleDerivedA D
  f_cycle_spec : f_cycle ≫ Abelian.image.ι D.alpha =
    kernel.ι (exactCoupleDifferential D) ≫ D.f
  f_spec : cokernel.π (exactCoupleDerivedBoundaryMap D) ≫ couple.f = f_cycle
  g_cycle : exactCoupleDerivedA D ⟶ kernel (exactCoupleDifferential D)
  g_cycle_spec : g_cycle ≫ kernel.ι (exactCoupleDifferential D) =
    Abelian.image.ι D.alpha ≫ D.g
  g_spec : g_cycle ≫ cokernel.π (exactCoupleDerivedBoundaryMap D) = couple.g

/-- The derived exact couple, with `A' = Im(alpha)` and
`E' = Ker(d)/Im(d)`. -/
theorem exactCoupleDerived_exists {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (ExactCoupleDerivedData D) := by
  sorry

noncomputable def exactCoupleDerivedData {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    ExactCoupleDerivedData D :=
  Classical.choice (exactCoupleDerived_exists D)

noncomputable def exactCoupleDerived {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    ExactCouple C (exactCoupleDerivedA D) (exactCoupleDerivedE D) :=
  (exactCoupleDerivedData D).couple

/- The induced maps are the maps of the chosen derived exact couple, so the
three names below cannot drift apart from its exactness data. -/
abbrev exactCoupleDerivedAlpha {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedA D ⟶ exactCoupleDerivedA D :=
  (exactCoupleDerived D).alpha

abbrev exactCoupleDerivedF {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedE D ⟶ exactCoupleDerivedA D :=
  (exactCoupleDerived D).f

abbrev exactCoupleDerivedG {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedA D ⟶ exactCoupleDerivedE D :=
  (exactCoupleDerived D).g

/-- `Ker(d) = f⁻¹(Ker(g)) = f⁻¹(Im(alpha))`. -/
theorem exactCouple_kernel_formula {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Subobject.mk (kernel.ι (exactCoupleDifferential D)) =
        (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) ∧
      (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) =
      (Subobject.pullback D.f).obj ((Subobject.«exists» D.alpha).obj ⊤) := by
  sorry

/-- `Im(d) = g(Im(f)) = g(Ker(alpha))`. -/
theorem exactCouple_image_formula {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    (Subobject.«exists» (exactCoupleDifferential D)).obj ⊤ =
        (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) ∧
      (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) =
        (Subobject.«exists» D.g).obj (Subobject.mk (kernel.ι D.alpha)) := by
  sorry

theorem exactCoupleDerived_is_exact {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (ExactCouple C (exactCoupleDerivedA D) (exactCoupleDerivedE D)) := by
  exact ⟨exactCoupleDerived D⟩

/-- The recursive powers of `alpha`, avoiding any choice of a monoid API on
endomorphism objects. -/
def exactCoupleAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => exactCoupleAlphaPow D n ≫ D.alpha

/-- The boundary subobject `B_(n+1) = g(Ker(alpha^n))`. -/
def exactCoupleBoundarySubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) (n : ℕ) : Subobject E :=
  (Subobject.«exists» D.g).obj
    ((Subobject.pullback (exactCoupleAlphaPow D n)).obj
      (Subobject.mk (kernel.ι (exactCoupleAlphaPow D n))))

/-- The cycle subobject `Z_(n+1) = f⁻¹(Im(alpha^n))`. -/
def exactCoupleCycleSubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) (n : ℕ) : Subobject E :=
  (Subobject.pullback D.f).obj
    ((Subobject.«exists» (exactCoupleAlphaPow D n)).obj ⊤)

/-- The filtration starts with `B₁ = 0` and `Z₁ = E`. -/
def exactCoupleB {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ℕ → Subobject E
  | 0 => ⊥
  | n + 1 => exactCoupleBoundarySubobject D n

def exactCoupleZ {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ℕ → Subobject E
  | 0 => ⊤
  | n + 1 => exactCoupleCycleSubobject D n

def IsSubobjectUnion {C : Type u} [Category.{v} C] {E : C}
    (F : ℕ → Subobject E) (B : Subobject E) : Prop :=
  (∀ n, F n ≤ B) ∧ ∀ Y, (∀ n, F n ≤ Y) → B ≤ Y

def IsSubobjectIntersection {C : Type u} [Category.{v} C] {E : C}
    (F : ℕ → Subobject E) (Z : Subobject E) : Prop :=
  (∀ n, Z ≤ F n) ∧ ∀ Y, (∀ n, Y ≤ F n) → Y ≤ Z

theorem exactCouple_boundary_le_cycle {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) :
    exactCoupleBoundarySubobject D n ≤ exactCoupleCycleSubobject D n := by
  sorry

/-- The page component `E_(n+1) = Z_(n+1)/B_(n+1)` in the exact-couple
description. -/
noncomputable def exactCouplePageComponent {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) : C :=
  subquotientObject (exactCoupleBoundarySubobject D n)
    (exactCoupleCycleSubobject D n) (exactCouple_boundary_le_cycle D n)

/-! ### The associated spectral sequence -/

theorem exactCouple_associatedSpectralSequence_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    ∃ S : PlainSpectralSequence C 1,
      Nonempty (plainPageObject S 1 ≅ E) ∧
        ∀ n : ℕ,
          Nonempty (plainPageObject S (n + 1 : ℤ) ≅
            exactCouplePageComponent D n) := by
  sorry

noncomputable def exactCoupleAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : PlainSpectralSequence C 1 :=
  Classical.choose (exactCouple_associatedSpectralSequence_exists D)

theorem exactCouple_associated_page_one
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (plainPageObject (exactCoupleAssociatedSpectralSequence D) 1 ≅ E) := by
  sorry

theorem exactCouple_associated_page_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    ∀ n : ℕ,
      Nonempty (plainPageObject (exactCoupleAssociatedSpectralSequence D)
        (n + 1 : ℤ) ≅ exactCouplePageComponent D n) := by
  sorry

noncomputable def exactCouplePageClassOfCycle {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ)
    {T : C} (z : T ⟶ (exactCoupleCycleSubobject D n : C)) :
    T ⟶ exactCouplePageComponent D n :=
  z ≫ cokernel.π (Subobject.ofLE (exactCoupleBoundarySubobject D n)
    (exactCoupleCycleSubobject D n) (exactCouple_boundary_le_cycle D n))

/-- A test-object formulation of the rule defining the next differential.
The boundary representative is required to be the class of `g ≫ y`, so the
interface retains the source's use of the exact-couple map `g`. -/
structure ExactCoupleDifferentialRule {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) where
  differential : exactCouplePageComponent (C := C) D n ⟶
    exactCouplePageComponent (C := C) D n
  differential_squared : differential ≫ differential = 0
  rule : ∀ {T : C}
    (x : T ⟶ (exactCoupleCycleSubobject (C := C) D n : C))
    (y : T ⟶ A),
    x ≫ (exactCoupleCycleSubobject D n).arrow ≫ D.f =
        y ≫ exactCoupleAlphaPow D n →
      ∃ yCycle : T ⟶ (exactCoupleCycleSubobject (C := C) D n : C),
        yCycle ≫ (exactCoupleCycleSubobject D n).arrow = y ≫ D.g ∧
          exactCouplePageClassOfCycle D n x ≫ differential =
            exactCouplePageClassOfCycle D n yCycle

theorem exactCouple_differential_rule
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    ∀ n : ℕ, Nonempty (ExactCoupleDifferentialRule D n) := by
  sorry

/-- The quotient-page identifications and differential compatibility carried
by the exact-couple construction. -/
structure ExactCoupleAssociatedData {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) where
  sequence : PlainSpectralSequence.{v, u, 0} C 1
  pageIso : ∀ n : ℕ,
    plainPageObject sequence (n + 1 : ℤ) ≅ exactCouplePageComponent D n
  differentialRule : ∀ n : ℕ, Nonempty (ExactCoupleDifferentialRule D n)
  differential_compatibility : ∀ n : ℕ,
    ∃ R : ExactCoupleDifferentialRule D n,
      plainPageDifferential sequence (n + 1 : ℤ) ≫ (pageIso n).hom =
        (pageIso n).hom ≫ R.differential

theorem exactCouple_associated_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (ExactCoupleAssociatedData D) := by
  sorry

noncomputable def exactCoupleAssociatedData
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ExactCoupleAssociatedData D :=
  Classical.choice (exactCouple_associated_data_exists D)

/-- If the indicated union and intersection exist, the exact-couple
filtration has `B∞ ⊆ Z∞` and hence a limit quotient. -/
theorem exactCouple_limit_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E)
    (hB : ∃ B : Subobject E, IsSubobjectUnion (exactCoupleB D) B)
    (hZ : ∃ Z : Subobject E, IsSubobjectIntersection (exactCoupleZ D) Z) :
    ∃ B Z : Subobject E,
      IsSubobjectUnion (exactCoupleB D) B ∧
      IsSubobjectIntersection (exactCoupleZ D) Z ∧ B ≤ Z := by
  sorry

/-! ### Shifted exact couples -/

/-- Exactness of a five-term complex. -/
def ExactFiveTerm {C : Type u} [Category.{v} C] [Abelian C]
    {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) : Prop :=
  ∃ (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0),
    (ShortComplex.mk a b hab).Exact ∧
      (ShortComplex.mk b c hbc).Exact ∧
      (ShortComplex.mk c d hcd).Exact

/-- A shifted exact couple.  `S` and `T` are Mathlib equivalences, matching
the source's shift-functor hypothesis; the displayed five-term complex is
kept as an exact-complex predicate. -/
structure ShiftedExactCouple (C : Type u) [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (A E : C) where
  alpha : A ⟶ T.inverse.obj A
  f : E ⟶ A
  g : A ⟶ S.functor.obj E
  Talpha : T.functor.obj A ⟶ A
  Talpha_spec : Talpha = T.functor.map alpha ≫ T.counitIso.hom.app A
  exact : ExactFiveTerm (T.functor.map f) Talpha g (S.functor.map f)

def shiftedExactCoupleDifferential {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) : E ⟶ S.functor.obj E :=
  D.f ≫ D.g

theorem shiftedExactCouple_differential_sq
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDifferential D ≫ S.functor.map (shiftedExactCoupleDifferential D) = 0 := by
  sorry

theorem shiftedExactCouple_derived_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    ∃ A' E' : C, Nonempty (ShiftedExactCouple C (T.trans S) T A' E') := by
  sorry

theorem shiftedExactCouple_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    ∃ X : TranslatedSpectralSequenceData C, X.r₀ = 1 ∧
      Nonempty (X.page 1 ≅ E) := by
  sorry

end Formalization.Books.Homology.Unit20
