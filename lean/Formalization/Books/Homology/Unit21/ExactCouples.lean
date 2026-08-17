import Formalization.Books.Homology.Unit20.ExactCouples
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Homological Algebra, Chapter 21: Spectral sequences: exact couples

The general spectral-sequence and exact-couple interfaces from the preceding
chapter are reused.  This file adds the source-facing derived-couple,
filtration, limit, and shifted-couple statements in their source order.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit21

/-! ## 21.1 Exact couples and their morphisms -/

/- The preceding chapter already uses Mathlib's exact short-complex interface.
These aliases keep that canonical representation available under the current
chapter namespace instead of introducing a parallel exactness predicate. -/

/-- An exact couple in an abelian category. -/
abbrev ExactCouple (C : Type u) [Category.{v} C] [Abelian C]
    (A E : C) := Formalization.Books.Homology.Unit20.ExactCouple C A E

/-- A morphism of exact couples. -/
abbrev ExactCoupleHom {C : Type u} [Category.{v} C] [Abelian C]
    {A E A' E' : C} (D : ExactCouple C A E) (D' : ExactCouple C A' E') :=
  Formalization.Books.Homology.Unit20.ExactCoupleHom D D'

/-- The differential `d = g ≫ f` of an exact couple. -/
def exactCoupleDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : E ⟶ E :=
  D.f ≫ D.g

theorem exactCoupleDifferential_sq {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    exactCoupleDifferential D ≫ exactCoupleDifferential D = 0 := by
  sorry

/-- The next `E`-object, `Ker(d) / Im(d)`. -/
noncomputable abbrev exactCoupleDerivedE {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) : C :=
  Formalization.Books.Homology.Unit20.differentialHomology
    (exactCoupleDifferential D) (exactCoupleDifferential_sq D)

/-- The next `A`-object, `Im(alpha)`. -/
abbrev exactCoupleDerivedA {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : C := Abelian.image D.alpha

/-- The existence of the derived exact couple. -/
theorem exactCoupleDerived_exists {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    Nonempty (ExactCouple C (exactCoupleDerivedA D) (exactCoupleDerivedE D)) := by
  sorry

/-- A chosen derived exact couple. -/
noncomputable def exactCoupleDerived {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    ExactCouple C (exactCoupleDerivedA D) (exactCoupleDerivedE D) :=
  Classical.choice (exactCoupleDerived_exists D)

/-- The induced map `alpha'` of the chosen derived exact couple. -/
abbrev exactCoupleDerivedAlpha {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedA D ⟶ exactCoupleDerivedA D :=
  (exactCoupleDerived D).alpha

/-- The induced map `f'` of the chosen derived exact couple. -/
abbrev exactCoupleDerivedF {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedE D ⟶ exactCoupleDerivedA D :=
  (exactCoupleDerived D).f

/-- The induced map `g'` of the chosen derived exact couple. -/
abbrev exactCoupleDerivedG {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    exactCoupleDerivedA D ⟶ exactCoupleDerivedE D :=
  (exactCoupleDerived D).g

/-- The three exactness assertions for the chosen derived couple. -/
theorem exactCoupleDerived_is_exact {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    (ShortComplex.mk (exactCoupleDerived D).alpha
      (exactCoupleDerived D).g (exactCoupleDerived D).alpha_g).Exact ∧
      (ShortComplex.mk (exactCoupleDerived D).g
        (exactCoupleDerived D).f (exactCoupleDerived D).g_f).Exact ∧
      (ShortComplex.mk (exactCoupleDerived D).f
        (exactCoupleDerived D).alpha (exactCoupleDerived D).f_alpha).Exact := by
  exact ⟨(exactCoupleDerived D).exact_alpha_g,
    (exactCoupleDerived D).exact_g_f, (exactCoupleDerived D).exact_f_alpha⟩

/-- `Ker(d) = f⁻¹(Ker(g)) = f⁻¹(Im(alpha))`. -/
theorem exactCouple_kernel_formula {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    Subobject.mk (kernel.ι (exactCoupleDifferential D)) =
        (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) ∧
      (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) =
        (Subobject.pullback D.f).obj
          ((Subobject.«exists» D.alpha).obj ⊤) := by
  sorry

/-- `Im(d) = g(Im(f)) = g(Ker(alpha))`. -/
theorem exactCouple_image_formula {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    (Subobject.«exists» (exactCoupleDifferential D)).obj ⊤ =
        (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) ∧
      (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) =
        (Subobject.«exists» D.g).obj (Subobject.mk (kernel.ι D.alpha)) := by
  sorry

/-! ## The associated spectral sequence -/

abbrev PlainSpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (r₀ : ℤ := 1) :=
  Formalization.Books.Homology.Unit20.PlainSpectralSequence C r₀

abbrev plainPageObject {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) : C :=
  Formalization.Books.Homology.Unit20.plainPageObject E r hr

abbrev plainPageDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {r₀ : ℤ} (E : PlainSpectralSequence C r₀) (r : ℤ)
    (hr : r₀ ≤ r := by lia) :
    plainPageObject E r hr ⟶ plainPageObject E r hr :=
  Formalization.Books.Homology.Unit20.plainPageDifferential E r hr

theorem exactCouple_associatedSpectralSequence_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (PlainSpectralSequence C 1) := by
  sorry

/-- The spectral sequence obtained by iterating the derived exact couple. -/
noncomputable def exactCoupleAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : PlainSpectralSequence C 1 :=
  Classical.choice (exactCouple_associatedSpectralSequence_exists D)

theorem exactCouple_associated_page_one
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (plainPageObject (exactCoupleAssociatedSpectralSequence D) 1 ≅ E) := by
  sorry

/-! ## The `Bᵣ` and `Zᵣ` filtration -/

/-- The iterated endomorphisms `alpha^n`. -/
def exactCoupleAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ℕ → (A ⟶ A)
  | 0 => 𝟙 A
  | n + 1 => exactCoupleAlphaPow D n ≫ D.alpha

/-- The boundary subobject `B_(n+1) = g(Ker(alpha^n))`. -/
def exactCoupleBoundarySubobject {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) : Subobject E :=
  (Subobject.«exists» D.g).obj
    (Subobject.mk (kernel.ι (exactCoupleAlphaPow D n)))

/-- The cycle subobject `Z_(n+1) = f⁻¹(Im(alpha^n))`. -/
def exactCoupleCycleSubobject {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) : Subobject E :=
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

theorem exactCouple_boundary_le_cycle {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) :
    exactCoupleBoundarySubobject D n ≤ exactCoupleCycleSubobject D n := by
  sorry

theorem exactCouple_B_le_Z {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) (r : ℕ) :
    exactCoupleB D r ≤ exactCoupleZ D r := by
  cases r with
  | zero => exact bot_le
  | succ n => exact exactCouple_boundary_le_cycle D n

/-- The complete filtration assertion, including its monotonicity. -/
theorem exactCouple_filtration {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    exactCoupleB D 0 = ⊥ ∧ exactCoupleZ D 0 = ⊤ ∧
      (∀ r, exactCoupleB D r ≤ exactCoupleB D (r + 1)) ∧
      (∀ r, exactCoupleZ D (r + 1) ≤ exactCoupleZ D r) ∧
      (∀ r, exactCoupleB D r ≤ exactCoupleZ D r) := by
  sorry

/-- The page component `E_(n+1) = Z_(n+1)/B_(n+1)`. -/
noncomputable def exactCouplePageComponent {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (exactCoupleBoundarySubobject D n)
    (exactCoupleCycleSubobject D n) (exactCouple_boundary_le_cycle D n)

/-- The class of a cycle in the page quotient. -/
noncomputable def exactCouplePageClassOfCycle {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ)
    {T : C} (z : T ⟶ (exactCoupleCycleSubobject D n : C)) :
    T ⟶ exactCouplePageComponent D n :=
  z ≫ cokernel.π (Subobject.ofLE (exactCoupleBoundarySubobject D n)
    (exactCoupleCycleSubobject D n) (exactCouple_boundary_le_cycle D n))

/-- The page quotient description of every page of the associated sequence. -/
theorem exactCouple_associated_page_quotient
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    ∀ n : ℕ,
      Nonempty (plainPageObject (exactCoupleAssociatedSpectralSequence D)
        (n + 1 : ℤ) ≅ exactCouplePageComponent D n) := by
  sorry

/-- A test-object formulation of the rule for `d_(n+1)`. -/
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

/-- The page identifications and differential compatibility for the associated
spectral sequence.  This enriches the canonical Mathlib spectral sequence
with the exact-couple quotient description used in the source. -/
structure ExactCoupleAssociatedData {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) where
  sequence : Formalization.Books.Homology.Unit20.PlainSpectralSequence.{v, u, 0} C 1
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

/-! ## The limit -/

/-- A least upper bound of a family of subobjects. -/
def IsSubobjectUnion {C : Type u} [Category.{v} C] {E : C}
    (F : ℕ → Subobject E) (B : Subobject E) : Prop :=
  (∀ n, F n ≤ B) ∧ ∀ Y, (∀ n, F n ≤ Y) → B ≤ Y

/-- A greatest lower bound of a family of subobjects. -/
def IsSubobjectIntersection {C : Type u} [Category.{v} C] {E : C}
    (F : ℕ → Subobject E) (Z : Subobject E) : Prop :=
  (∀ n, Z ≤ F n) ∧ ∀ Y, (∀ n, Y ≤ F n) → Y ≤ Z

/-- The limit data supplied by the union and intersection in the source. -/
structure ExactCoupleLimitData {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) where
  Binf : Subobject E
  Zinf : Subobject E
  Binf_union : IsSubobjectUnion (exactCoupleB D) Binf
  Zinf_intersection : IsSubobjectIntersection (exactCoupleZ D) Zinf
  Binf_le_Zinf : Binf ≤ Zinf

/-- The source's inclusion `B∞ ≤ Z∞`, assuming actual union and intersection. -/
theorem exactCouple_limit_inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E)
    (hB : ∃ B : Subobject E, IsSubobjectUnion (exactCoupleB D) B)
    (hZ : ∃ Z : Subobject E, IsSubobjectIntersection (exactCoupleZ D) Z) :
    ∃ B Z : Subobject E,
      IsSubobjectUnion (exactCoupleB D) B ∧
      IsSubobjectIntersection (exactCoupleZ D) Z ∧ B ≤ Z := by
  sorry

theorem exactCouple_limit_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E)
    (hB : ∃ B : Subobject E, IsSubobjectUnion (exactCoupleB D) B)
    (hZ : ∃ Z : Subobject E, IsSubobjectIntersection (exactCoupleZ D) Z) :
    Nonempty (ExactCoupleLimitData D) := by
  sorry

/-- The limit object `E∞ = Z∞/B∞`. -/
noncomputable def exactCoupleLimitObject
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) (L : ExactCoupleLimitData D) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject L.Binf L.Zinf
    L.Binf_le_Zinf

/-! ## 21.1 shifted exact couples -/

/-- Exactness of the five-term complex in the shifted variant. -/
abbrev ExactFiveTerm {C : Type u} [Category.{v} C] [Abelian C]
    {X₀ X₁ X₂ X₃ X₄ : C}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄) : Prop :=
  Formalization.Books.Homology.Unit20.ExactFiveTerm a b c d

/-- A shifted exact couple for the equivalences `S` and `T`. -/
abbrev ShiftedExactCouple (C : Type u) [Category.{v} C] [Abelian C]
    (S T : C ≌ C) (A E : C) :=
  Formalization.Books.Homology.Unit20.ShiftedExactCouple C S T A E

/-- The shifted differential `d : E ⟶ S(E)`. -/
def shiftedExactCoupleDifferential {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) : E ⟶ S.functor.obj E :=
  D.f ≫ D.g

/-- The translated previous differential `S⁻¹d : S⁻¹E ⟶ E`. -/
def shiftedExactCouplePreviousDifferential {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) : S.inverse.obj E ⟶ E :=
  Formalization.Books.Homology.Unit20.translatedPreviousDifferential S
    (shiftedExactCoupleDifferential D)

theorem shiftedExactCouple_differential_previous_comp
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCouplePreviousDifferential D ≫
      shiftedExactCoupleDifferential D = 0 := by
  sorry

theorem shiftedExactCouple_differential_sq
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDifferential D ≫
      S.functor.map (shiftedExactCoupleDifferential D) = 0 := by
  sorry

/-- The shifted derived `E`-object `Ker(d)/Im(S⁻¹d)`. -/
noncomputable def shiftedExactCoupleDerivedE {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) : C :=
  Formalization.Books.Homology.Unit20.translatedDifferentialHomology S
    (shiftedExactCoupleDifferential D) (shiftedExactCouple_differential_sq D)

/-- The shifted derived `A`-object `Im(T alpha)`. -/
noncomputable def shiftedExactCoupleDerivedA {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) : C := Abelian.image D.Talpha

/-- The existence of the derived couple, whose new shifts are `TS` and `T`. -/
theorem shiftedExactCoupleDerived_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    Nonempty (ShiftedExactCouple C (T.trans S) T
      (shiftedExactCoupleDerivedA D) (shiftedExactCoupleDerivedE D)) := by
  sorry

/-- A chosen shifted derived exact couple. -/
noncomputable def shiftedExactCoupleDerived
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    ShiftedExactCouple C (T.trans S) T
      (shiftedExactCoupleDerivedA D) (shiftedExactCoupleDerivedE D) :=
  Classical.choice (shiftedExactCoupleDerived_exists D)

abbrev shiftedExactCoupleDerivedAlpha {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDerivedA D ⟶
      T.inverse.obj (shiftedExactCoupleDerivedA D) :=
  (shiftedExactCoupleDerived D).alpha

abbrev shiftedExactCoupleDerivedF {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDerivedE D ⟶ shiftedExactCoupleDerivedA D :=
  (shiftedExactCoupleDerived D).f

abbrev shiftedExactCoupleDerivedG {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDerivedA D ⟶
      (T.trans S).functor.obj (shiftedExactCoupleDerivedE D) :=
  (shiftedExactCoupleDerived D).g

theorem shiftedExactCoupleDerived_is_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    ExactFiveTerm (T.functor.map (shiftedExactCoupleDerived D).f)
      (shiftedExactCoupleDerived D).Talpha
      (shiftedExactCoupleDerived D).g
      ((T.trans S).functor.map (shiftedExactCoupleDerived D).f) :=
  (shiftedExactCoupleDerived D).exact

/-- `Ker(d) = f⁻¹(Ker(g)) = f⁻¹(Im(T alpha))`. -/
theorem shiftedExactCouple_kernel_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    Subobject.mk (kernel.ι (shiftedExactCoupleDifferential D)) =
        (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) ∧
      (Subobject.pullback D.f).obj (Subobject.mk (kernel.ι D.g)) =
        (Subobject.pullback D.f).obj
          ((Subobject.«exists» D.Talpha).obj ⊤) := by
  sorry

/-- `Im(d) = g(Im(f)) = g(Ker(alpha))` in the shifted setting. -/
theorem shiftedExactCouple_image_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    (Subobject.«exists» (shiftedExactCoupleDifferential D)).obj ⊤ =
        (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) ∧
      (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) =
        (Subobject.«exists» D.g).obj (Subobject.mk (kernel.ι D.alpha)) := by
  sorry

/-! ### Iterated shifts and the associated translated sequence -/

/-- The corresponding `n`-fold composition as a categorical equivalence. -/
def shiftedEquivalenceIterate {C : Type u} [Category.{v} C]
    (T : C ≌ C) (n : ℕ) : C ≌ C :=
  match n with
  | 0 => CategoryTheory.Equivalence.refl
  | n + 1 => T.trans (shiftedEquivalenceIterate T n)

/-- The iterated composite `T⁻ⁿ alpha : A ⟶ T⁻ⁿ A`. -/
def shiftedExactCoupleInverseAlphaPow {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    ∀ n : ℕ, A ⟶ (shiftedEquivalenceIterate T.symm n).functor.obj A
  | 0 => 𝟙 A
  | n + 1 => shiftedExactCoupleInverseAlphaPow D n ≫
      (shiftedEquivalenceIterate T.symm n).functor.map D.alpha

/-- The iterated composite `T alpha ... Tⁿ alpha : Tⁿ A ⟶ A`. -/
def shiftedExactCoupleTAlphaPow {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    ∀ n : ℕ, (shiftedEquivalenceIterate T n).functor.obj A ⟶ A
  | 0 => 𝟙 A
  | n + 1 =>
      (shiftedEquivalenceIterate T n).functor.map D.Talpha ≫
        shiftedExactCoupleTAlphaPow D n

/-- The shifted boundary formula
`SB_(n+1) = g(Ker(T⁻ⁿ alpha ... alpha))`. -/
def shiftedExactCoupleBoundarySubobject {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) (n : ℕ) :
    Subobject (S.functor.obj E) :=
  (Subobject.«exists» D.g).obj
    (Subobject.mk (kernel.ι (shiftedExactCoupleInverseAlphaPow D n)))

/-- The shifted cycle formula
`Z_(n+1) = f⁻¹(Im(T alpha ... Tⁿ alpha))`. -/
def shiftedExactCoupleCycleSubobject {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) (n : ℕ) : Subobject E :=
  (Subobject.pullback D.f).obj
    ((Subobject.«exists» (shiftedExactCoupleTAlphaPow D n)).obj ⊤)

theorem shiftedExactCouple_boundary_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) (n : ℕ) :
    shiftedExactCoupleBoundarySubobject D n =
      (Subobject.«exists» D.g).obj
        (Subobject.mk (kernel.ι (shiftedExactCoupleInverseAlphaPow D n))) := rfl

theorem shiftedExactCouple_cycle_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) (n : ℕ) :
    shiftedExactCoupleCycleSubobject D n =
      (Subobject.pullback D.f).obj
        ((Subobject.«exists» (shiftedExactCoupleTAlphaPow D n)).obj ⊤) := rfl

abbrev TranslatedSpectralSequence (C : Type u) [Category.{v} C]
    [Abelian C] := Formalization.Books.Homology.Unit20.TranslatedSpectralSequence C

/-- The translation `T^(r-1) S` used on page `r` for `r ≥ 1`. -/
def shiftedExactCoupleTranslation {C : Type u} [Category.{v} C]
    (S T : C ≌ C) (r : ℤ) : C ≌ C :=
  if 1 ≤ r then
    (shiftedEquivalenceIterate T (Int.toNat (r - 1))).trans S
  else S

/-- A translated spectral sequence associated to a shifted exact couple. -/
structure ShiftedExactCoupleAssociatedSpectralSequence
    (C : Type u) [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) where
  sequence : TranslatedSpectralSequence C
  starts_at_one : sequence.r₀ = 1
  translation : ∀ r, sequence.translation r =
    shiftedExactCoupleTranslation S T r
  page_one : Nonempty (sequence.page 1 ≅ E)

theorem shiftedExactCouple_associatedSpectralSequence_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    Nonempty (ShiftedExactCoupleAssociatedSpectralSequence (C := C) D) := by
  sorry

noncomputable def shiftedExactCoupleAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    ShiftedExactCoupleAssociatedSpectralSequence (C := C) D :=
  Classical.choice (shiftedExactCouple_associatedSpectralSequence_exists D)

theorem shiftedExactCouple_translation_formula
    {C : Type u} [Category.{v} C]
    (S T : C ≌ C) (r : ℤ) (hr : 1 ≤ r) :
    shiftedExactCoupleTranslation S T r =
      (shiftedEquivalenceIterate T (Int.toNat (r - 1))).trans S := by
  simp [shiftedExactCoupleTranslation, hr]

end Formalization.Books.Homology.Unit21
