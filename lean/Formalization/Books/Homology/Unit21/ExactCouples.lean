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

/-- The differential `d = f ≫ g` (that is, `g ∘ f`) of an exact couple. -/
def exactCoupleDifferential {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : E ⟶ E :=
  D.f ≫ D.g

theorem exactCoupleDifferential_sq {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    exactCoupleDifferential D ≫ exactCoupleDifferential D = 0 := by
  exact Formalization.Books.Homology.Unit20.exactCoupleDifferential_sq D

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
  exact ⟨(Classical.choice
    (Formalization.Books.Homology.Unit20.exactCoupleDerived_exists D)).couple⟩

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
  exact Formalization.Books.Homology.Unit20.exactCouple_kernel_formula D

/-- `Im(d) = g(Im(f)) = g(Ker(alpha))`. -/
theorem exactCouple_image_formula {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) :
    (Subobject.«exists» (exactCoupleDifferential D)).obj ⊤ =
        (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) ∧
      (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) =
        (Subobject.«exists» D.g).obj (Subobject.mk (kernel.ι D.alpha)) := by
  exact Formalization.Books.Homology.Unit20.exactCouple_image_formula D

/-! ## The `Bᵣ` and `Zᵣ` filtration -/

/-- The iterated endomorphisms `alpha^n`. -/
abbrev exactCoupleAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : ℕ → (A ⟶ A)
  := Formalization.Books.Homology.Unit20.exactCoupleAlphaPow D

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
  let P := (Subobject.«exists» (exactCoupleAlphaPow D n)).obj (⊤ : Subobject A)
  let K := Subobject.mk (kernel.ι (exactCoupleAlphaPow D n))
  let B := exactCoupleBoundarySubobject D n
  let F := Subobject.imageFactorisation D.g K
  have hB : B.arrow ≫ D.f = 0 := by
    change F.F.m ≫ D.f = 0
    let _ : Epi F.F.e :=
      (strongEpi_of_strongEpiMonoFactorisation
        (Abelian.imageStrongEpiMonoFactorisation (K.arrow ≫ D.g)) F.isImage).epi
    apply (cancel_epi F.F.e).mp
    rw [← Category.assoc, F.F.fac, Category.assoc, D.g_f]
    simp
  let hpb := Subobject.isPullback D.f P
  have hpbcond : 0 ≫ P.arrow = B.arrow ≫ D.f := by
    rw [zero_comp]
    exact hB.symm
  exact Subobject.le_of_comm
    (hpb.lift 0 B.arrow hpbcond)
    (by
      simp [P, exactCoupleCycleSubobject, B])

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
  have hker : ∀ n : ℕ,
      Subobject.mk (kernel.ι (exactCoupleAlphaPow D n)) ≤
        Subobject.mk (kernel.ι (exactCoupleAlphaPow D (n + 1))) := by
    intro n
    have hzero :
        kernel.ι (exactCoupleAlphaPow D n) ≫ exactCoupleAlphaPow D (n + 1) = 0 := by
      rw [show exactCoupleAlphaPow D (n + 1) =
          exactCoupleAlphaPow D n ≫ D.alpha by rfl, ← Category.assoc,
        kernel.condition]
      simp
    let k := kernel.lift (exactCoupleAlphaPow D (n + 1))
      (kernel.ι (exactCoupleAlphaPow D n)) hzero
    apply Subobject.le_mk_of_comm
      ((Subobject.underlyingIso (kernel.ι (exactCoupleAlphaPow D n))).hom ≫ k)
    dsimp [k]
    rw [Category.assoc, kernel.lift_ι]
    exact Subobject.underlyingIso_hom_comp_eq_mk _
  have hpow_comm : ∀ n : ℕ,
      D.alpha ≫ exactCoupleAlphaPow D n =
        exactCoupleAlphaPow D n ≫ D.alpha := by
    intro n
    induction n with
    | zero =>
        simp [exactCoupleAlphaPow,
          Formalization.Books.Homology.Unit20.exactCoupleAlphaPow]
    | succ n ih =>
        rw [show exactCoupleAlphaPow D (n + 1) =
            exactCoupleAlphaPow D n ≫ D.alpha by rfl]
        rw [← Category.assoc, ih]
  have hexists {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z) (P : Subobject X) :
      (Subobject.«exists» (a ≫ b)).obj P =
        (Subobject.«exists» b).obj ((Subobject.«exists» a).obj P) := by
    apply le_antisymm
    · have h : P ≤ (Subobject.pullback (a ≫ b)).obj
          ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)) := by
        rw [Subobject.pullback_comp]
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj
            ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))))
          (CategoryTheory.homOfLE
            (((Subobject.existsPullbackAdj b).homEquiv
              ((Subobject.«exists» a).obj P)
              ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)))
              (CategoryTheory.homOfLE le_rfl)).le) |>.le
      exact ((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
        ((Subobject.«exists» b).obj ((Subobject.«exists» a).obj P))).symm
        (CategoryTheory.homOfLE h) |>.le
    · have h : (Subobject.«exists» a).obj P ≤
          (Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P) := by
        have h' : P ≤ (Subobject.pullback (a ≫ b)).obj
            ((Subobject.«exists» (a ≫ b)).obj P) :=
          (((Subobject.existsPullbackAdj (a ≫ b)).homEquiv P
            ((Subobject.«exists» (a ≫ b)).obj P))
            (CategoryTheory.homOfLE le_rfl)).le
        rw [Subobject.pullback_comp] at h'
        exact ((Subobject.existsPullbackAdj a).homEquiv P
          ((Subobject.pullback b).obj ((Subobject.«exists» (a ≫ b)).obj P))).symm
          (CategoryTheory.homOfLE h') |>.le
      exact ((Subobject.existsPullbackAdj b).homEquiv
        ((Subobject.«exists» a).obj P)
        ((Subobject.«exists» (a ≫ b)).obj P)).symm
        (CategoryTheory.homOfLE h) |>.le
  have himage : ∀ n : ℕ,
      (Subobject.«exists» (exactCoupleAlphaPow D (n + 1))).obj (⊤ : Subobject A) ≤
        (Subobject.«exists» (exactCoupleAlphaPow D n)).obj ⊤ := by
    intro n
    have hpow :
        exactCoupleAlphaPow D (n + 1) =
          D.alpha ≫ exactCoupleAlphaPow D n := by
      rw [show exactCoupleAlphaPow D (n + 1) =
          exactCoupleAlphaPow D n ≫ D.alpha by rfl, hpow_comm]
    rw [hpow, hexists]
    exact (Subobject.«exists» (exactCoupleAlphaPow D n)).monotone
      (le_top :
        (Subobject.«exists» D.alpha).obj (⊤ : Subobject A) ≤ ⊤)
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · intro r
    cases r with
    | zero => exact bot_le
    | succ n =>
        simpa [exactCoupleB, exactCoupleBoundarySubobject] using
          (Subobject.«exists» D.g).monotone (hker n)
  · intro r
    cases r with
    | zero => exact le_top
    | succ n =>
        simpa [exactCoupleZ, exactCoupleCycleSubobject] using
          (Subobject.pullback D.f).monotone (himage n)
  · exact exactCouple_B_le_Z D

/-- The page component `E_(n+1) = Z_(n+1)/B_(n+1)`. -/
noncomputable def exactCouplePageComponent {C : Type u} [Category.{v} C]
    [Abelian C] {A E : C} (D : ExactCouple C A E) (n : ℕ) : C :=
  Formalization.Books.Homology.Unit20.subquotientObject
    (exactCoupleBoundarySubobject D n)
    (exactCoupleCycleSubobject D n) (exactCouple_boundary_le_cycle D n)

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
  obtain ⟨S, _, _⟩ :=
    Formalization.Books.Homology.Unit20.exactCouple_associatedSpectralSequence_exists D
  exact ⟨S⟩

private theorem exactCouplePageComponent_eq_unit20
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) (n : ℕ) :
    exactCouplePageComponent D n =
      Formalization.Books.Homology.Unit20.exactCouplePageComponent D n := by
  simp [exactCouplePageComponent,
    Formalization.Books.Homology.Unit20.exactCouplePageComponent,
    exactCoupleBoundarySubobject,
    Formalization.Books.Homology.Unit20.exactCoupleBoundarySubobject,
    exactCoupleCycleSubobject,
    Formalization.Books.Homology.Unit20.exactCoupleCycleSubobject]

/-- The chosen sequence and its page identifications must come from one
    witness, since an arbitrary choice of a merely nonempty sequence need not
    be the sequence carrying these identifications. -/
theorem exactCouple_associatedSpectralSequence_witness_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    ∃ S : PlainSpectralSequence C 1,
      Nonempty (plainPageObject S 1 ≅ E) ∧
      ∀ n : ℕ,
        Nonempty (plainPageObject S (n + 1 : ℤ) ≅ exactCouplePageComponent D n) := by
  obtain ⟨S, hE, hpage⟩ :=
    Formalization.Books.Homology.Unit20.exactCouple_associatedSpectralSequence_transport D
      (fun n => exactCouplePageComponent D n) (by
        intro n
        exact ⟨eqToIso (exactCouplePageComponent_eq_unit20 D n).symm⟩)
  exact ⟨S, hE, hpage⟩

/-- The spectral sequence obtained by iterating the derived exact couple. -/
noncomputable def exactCoupleAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) : PlainSpectralSequence C 1 :=
  Classical.choose (exactCouple_associatedSpectralSequence_witness_exists D)

theorem exactCouple_associated_page_one
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E) :
    Nonempty (plainPageObject (exactCoupleAssociatedSpectralSequence D) 1 ≅ E) := by
  exact (Classical.choose_spec
    (exactCouple_associatedSpectralSequence_witness_exists D)).1

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
  exact (Classical.choose_spec
    (exactCouple_associatedSpectralSequence_witness_exists D)).2

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
  /-
  Proof roadmap.

  * Transport the rule already supplied by
    `Formalization.Books.Homology.Unit20.exactCouple_differential_rule` in
    `Unit20/ExactCouples.lean`; a direct `exact` cannot work because the two
    chapters deliberately have distinct structure names.
  * For fixed `n`, obtain an upstream rule `R` and rebuild the local structure
    fieldwise as `ExactCoupleDifferentialRule.mk R.differential
    R.differential_squared _`.  The two page-component types are
    definitionally equal after proof irrelevance; a tactic trial confirms
    that the two displayed fields elaborate without any cast.
  * The cycle subobjects, powers of `alpha`, and class maps are likewise
    definitionally the same in the two chapters.  Apply `R.rule x y` to the
    given factorisation (use
    `simpa [exactCoupleCycleSubobject, exactCoupleAlphaPow,
    Formalization.Books.Homology.Unit20.exactCoupleCycleSubobject]`).  Reuse
    its `yCycle` and both conclusions.  If simplification stops at the quotient
    object, unfold both versions of `exactCouplePageClassOfCycle`; proof
    irrelevance identifies their `exactCouple_boundary_le_cycle` arguments.
  * Keep this fieldwise conversion as a local function so that
    `exactCouple_associated_data_exists` below can convert the specific
    upstream rule occurring in its compatibility equation, then return the
    converted rule for every `n`.
  -/
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
  /-
  Proof roadmap.

  * Obtain `⟨U⟩` from
    `Formalization.Books.Homology.Unit20.exactCouple_associated_data_exists D`
    (`Unit20/ExactCouples.lean`), instantiated as
    `PlainSpectralSequence.{v, u, 0} C 1`.  Keep `U.sequence`; do not use the
    separately chosen `exactCoupleAssociatedSpectralSequence`, because its
    choice is not tied to `U.differential_compatibility`.
  * Use `U.pageIso` fieldwise: Unit20 and Unit21 page components are
    definitionally equal after proof irrelevance.  If elaboration exposes the
    equality, use the already proved `exactCouplePageComponent_eq_unit20 D n`
    and set `pageIso n := U.pageIso n ≪≫
    (eqToIso (exactCouplePageComponent_eq_unit20 D n)).symm`.
  * Set `differentialRule := exactCouple_differential_rule D`.  For
    compatibility, obtain `⟨R₂₀, hR₂₀⟩ :=
    U.differential_compatibility n` and convert this *same* `R₂₀` by the
    fieldwise construction in the preceding roadmap.  Its differential is
    definitionally `R₂₀.differential`, so `simpa` turns `hR₂₀` into exactly
    `plainPageDifferential U.sequence (n + 1 : ℤ) ≫ (pageIso n).hom =
    (pageIso n).hom ≫ R.differential`.  In the explicit-iso fallback,
    conjugate the converted differential by that iso and cancel its inverse
    and hom after reassociating `hR₂₀`.  Assemble the four structure fields and
    wrap the result in `Nonempty`.
  -/
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
  obtain ⟨B, hB⟩ := hB
  obtain ⟨Z, hZ⟩ := hZ
  refine ⟨B, Z, hB, hZ, ?_⟩
  have hfil := exactCouple_filtration D
  have hBmono : ∀ {m n : ℕ}, m ≤ n → exactCoupleB D m ≤ exactCoupleB D n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hmn ih =>
        exact le_trans ih (hfil.2.2.1 n)
  have hZmono : ∀ {m n : ℕ}, m ≤ n → exactCoupleZ D n ≤ exactCoupleZ D m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hmn ih =>
        exact le_trans (hfil.2.2.2.1 n) ih
  apply hZ.2 B
  intro n
  apply hB.2 (exactCoupleZ D n)
  intro m
  rcases le_total m n with hmn | hnm
  · exact le_trans (hBmono hmn) (hfil.2.2.2.2 n)
  · exact le_trans (hfil.2.2.2.2 m) (hZmono hnm)

theorem exactCouple_limit_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A E : C} (D : ExactCouple C A E)
    (hB : ∃ B : Subobject E, IsSubobjectUnion (exactCoupleB D) B)
    (hZ : ∃ Z : Subobject E, IsSubobjectIntersection (exactCoupleZ D) Z) :
    Nonempty (ExactCoupleLimitData D) := by
  obtain ⟨B, Z, hBu, hZi, hBZ⟩ := exactCouple_limit_inclusion D hB hZ
  exact ⟨ExactCoupleLimitData.mk B Z hBu hZi hBZ⟩

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
  have hsq : shiftedExactCoupleDifferential D ≫
      S.functor.map (shiftedExactCoupleDifferential D) = 0 := by
    rcases D.exact with ⟨_, _, hcd, _⟩
    rw [shiftedExactCoupleDifferential, Functor.map_comp]
    calc
      (D.f ≫ D.g) ≫ S.functor.map D.f ≫ S.functor.map D.g =
          D.f ≫ ((D.g ≫ S.functor.map D.f) ≫ S.functor.map D.g) := by
            simp only [Category.assoc]
      _ = 0 := by rw [hcd, zero_comp, comp_zero]
  simpa [shiftedExactCouplePreviousDifferential, shiftedExactCoupleDifferential] using
    Formalization.Books.Homology.Unit20.translatedPreviousDifferential_comp
      (shiftedExactCoupleDifferential D) hsq

theorem shiftedExactCouple_differential_sq
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C}
    (D : ShiftedExactCouple C S T A E) :
    shiftedExactCoupleDifferential D ≫
      S.functor.map (shiftedExactCoupleDifferential D) = 0 := by
  rcases D.exact with ⟨_, _, hcd, _⟩
  rw [shiftedExactCoupleDifferential, Functor.map_comp]
  calc
    (D.f ≫ D.g) ≫ S.functor.map D.f ≫ S.functor.map D.g =
        D.f ≫ ((D.g ≫ S.functor.map D.f) ≫ S.functor.map D.g) := by
          simp only [Category.assoc]
    _ = 0 := by rw [hcd, zero_comp, comp_zero]

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
    Nonempty (ShiftedExactCouple C (S.trans T) T
      (shiftedExactCoupleDerivedA D) (shiftedExactCoupleDerivedE D)) := by
  /-
  Proof roadmap.

  The order `S.trans T` is intentional: by `Equivalence.trans` in
  `Mathlib/CategoryTheory/Equivalence.lean` its functor is `S.functor ⋙
  T.functor`, hence its value is the source's `TS`.  Do not apply
  `Unit20.shiftedExactCouple_derived_exists`; that declaration concludes with
  `T.trans S`, has unspecified `A'` and `E'`, and cannot be transported
  without an extra commutation isomorphism.

  * Abbreviate `d := shiftedExactCoupleDifferential D`,
    `p := shiftedExactCouplePreviousDifferential D`, and
    `b := kernel.lift d (Abelian.image.ι p)
      (by simpa using shiftedExactCouple_differential_previous_comp D)`.
    Then the required `E'` unfolds to `cokernel b`; write
    `q := cokernel.π b : kernel d ⟶ E'`.  Write
    `A' := Abelian.image D.Talpha` and `iA := Abelian.image.ι D.Talpha`.
  * Extract the three zero composites and exactness witnesses from `D.exact`.
    Define the restriction
    `Talpha' : T.functor.obj A' ⟶ A'` by
    `T.functor.map iA ≫ Abelian.factorThruImage D.Talpha`.  Define
    `alpha' : A' ⟶ T.inverse.obj A'` by transporting `Talpha'` through
    `T.unitIso`; the triangle identities prove
    `Talpha' = T.functor.map alpha' ≫ T.counitIso.hom.app A'`.
  * Construct `fCycle : kernel d ⟶ A'` with
    `ShortComplex.Exact.isLimitImage` (`Mathlib/CategoryTheory/Abelian/Exact.lean`)
    for the exact pair `(D.Talpha, D.g)`: its composite with `iA` is
    `kernel.ι d ≫ D.f`.  Show `b ≫ fCycle = 0` after cancelling the
    mono `iA`; unfold `p` and use the exact-couple zero composite
    `D.g ≫ S.functor.map D.f = 0`.  Set
    `f' := cokernel.desc b fCycle this`.
  * For `g'`, first factor `T.functor.map D.g` through the kernel of
    `(S.trans T).functor.map d`.  Use `Limits.PreservesKernel.iso` from
    `Mathlib/CategoryTheory/Limits/Preserves/Shapes/Kernels.lean` to identify
    that kernel with `(S.trans T).functor.obj (kernel d)`, then compose with
    `(S.trans T).functor.map q`.  Call the resulting map
    `g0 : T.functor.obj A ⟶ (S.trans T).functor.obj E'`.
    Prove `kernel.ι D.Talpha ≫ g0 = 0`: exactness of
    `(T.functor.map D.f, D.Talpha)` identifies this kernel with the image of
    `T.functor.map D.f`, while `q` kills the transported image of `p`
    (which is the image of `T.functor.map d`).  Descend `g0` through
    `cokernel (kernel.ι D.Talpha)` and precompose with
    `(Abelian.coimageIsoImage D.Talpha).inv` to obtain
    `g' : A' ⟶ (S.trans T).functor.obj E'`.
  * Prove the three image/kernel equalities for
    `(T.functor.map f', Talpha', g', (S.trans T).functor.map f')` by the same
    kernel/cokernel universal properties.  Convert them to exactness with
    `ShortComplex.exact_iff_image_eq_kernel`; the required zero composites
    are the equations used to define the descents.  Finally fill the five
    fields of `Unit20.ShiftedExactCouple` and return it in `Nonempty`.
  -/
  sorry

/-- A chosen shifted derived exact couple. -/
noncomputable def shiftedExactCoupleDerived
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    ShiftedExactCouple C (S.trans T) T
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
      (S.trans T).functor.obj (shiftedExactCoupleDerivedE D) :=
  (shiftedExactCoupleDerived D).g

theorem shiftedExactCoupleDerived_is_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    ExactFiveTerm (T.functor.map (shiftedExactCoupleDerived D).f)
      (shiftedExactCoupleDerived D).Talpha
      (shiftedExactCoupleDerived D).g
      ((S.trans T).functor.map (shiftedExactCoupleDerived D).f) :=
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
  /-
  Proof roadmap.

  * Prove the generic identity
    `kernelSubobject (f ≫ g) =
      (Subobject.pullback f).obj (kernelSubobject g)` by antisymmetry.
    For the forward map use `kernel.lift g (kernel.ι (f ≫ g) ≫ f)` and
    `Subobject.isPullback`; for the reverse map use the same pullback square,
    `kernel.lift (f ≫ g)`, `Subobject.le_of_comm`, and
    `Subobject.le_mk_of_comm`.  The needed API is in
    `Mathlib/CategoryTheory/Subobject/Basic.lean` and
    `Mathlib/CategoryTheory/Subobject/Limits.lean`.  Specialise to `D.f` and
    `D.g`, then unfold `shiftedExactCoupleDifferential`.
  * From `D.exact`, retain the middle exactness witness for the pair
    `(D.Talpha, D.g)`.  Apply
    `ShortComplex.exact_iff_image_eq_kernel` from
    `Mathlib/CategoryTheory/Abelian/Exact.lean` to get
    `imageSubobject D.Talpha = kernelSubobject D.g`.
  * Identify `(Subobject.«exists» D.Talpha).obj ⊤` with
    `imageSubobject D.Talpha`.  A robust proof uses
    `Subobject.existsIsoImage`, `Subobject.imageSubobjectIso`, and
    `Subobject.eq_of_comm`; do not rely on definitional reduction of the
    chosen image factorisation.  Rewrite by the exactness equality and apply
    congruence of `(Subobject.pullback D.f).obj` for the second conjunct.
  -/
  sorry

/-- `Im(d) = g(Im(f)) = g(Ker(alpha))` in the shifted setting. -/
theorem shiftedExactCouple_image_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {S T : C ≌ C} {A E : C} (D : ShiftedExactCouple C S T A E) :
    (Subobject.«exists» (shiftedExactCoupleDifferential D)).obj ⊤ =
        (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) ∧
      (Subobject.«exists» D.g).obj ((Subobject.«exists» D.f).obj ⊤) =
        (Subobject.«exists» D.g).obj (Subobject.mk (kernel.ι D.alpha)) := by
  /-
  Proof roadmap.

  * First prove/hoist the generic composition formula already established
    inside `exactCouple_filtration` above:
    `(Subobject.«exists» (a ≫ b)).obj P =
      (Subobject.«exists» b).obj ((Subobject.«exists» a).obj P)`.
    Its proof uses the adjunction `Subobject.existsPullbackAdj` and
    `Subobject.pullback_comp` from
    `Mathlib/CategoryTheory/Subobject/Basic.lean`.  Apply it to `D.f`, `D.g`,
    and `P = ⊤`, then unfold `shiftedExactCoupleDifferential`; this is the
    first conjunct.
  * Extract the first exact pair `(T.functor.map D.f, D.Talpha)` from
    `D.exact`.  Map that short complex by `T.inverse`.  Exactness is preserved
    by `ShortComplex.Exact.map` in
    `Mathlib/Algebra/Homology/ShortComplex/Exact.lean`.  Build a
    `ShortComplex.isoMk` (from `.../ShortComplex/Basic.lean`) from the mapped
    complex to `ShortComplex.mk D.f D.alpha _`.  Obtain its zero proof by
    applying the faithful functor `T.functor` to `D.f ≫ D.alpha`, rewriting
    with `D.Talpha_spec`, and using the zero composite
    `T.functor.map D.f ≫ D.Talpha = 0`.  Use
    `(T.unitIso.app E).symm`, `(T.unitIso.app A).symm`, and `Iso.refl _`;
    `D.Talpha_spec`, naturality, and the equivalence triangle identities prove
    its two commutative squares.
  * Transfer exactness across that isomorphism with
    `ShortComplex.exact_iff_of_iso`, then use
    `ShortComplex.exact_iff_image_eq_kernel` to obtain
    `imageSubobject D.f = kernelSubobject D.alpha`.  Rewrite
    `imageSubobject D.f` as `(Subobject.«exists» D.f).obj ⊤` using the
    `Subobject.existsIsoImage` argument from the kernel roadmap, and apply
    congruence of `(Subobject.«exists» D.g).obj` to finish the second
    conjunct.
  -/
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
    S.trans (shiftedEquivalenceIterate T (Int.toNat (r - 1)))
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
  /-
  Proof roadmap.

  The Unit20 existence theorem only fixes `r₀` and page one; it does not
  constrain `sequence.translation`, so refining its witness cannot prove this
  statement.  Construct the weak translated sequence required by this
  structure directly.

  * Let `τ r := shiftedExactCoupleTranslation S T r`.  Define pages for
    natural offsets by
    `P 0 := E` and
    `P (n + 1) := Unit20.translatedDifferentialHomology
      (τ (Int.ofNat (n + 1))) (0 : P n ⟶ (τ _).functor.obj (P n))
      (by simp)`; this uses `translatedDifferentialHomology` from
    `Unit20/SpectralSequences.lean`.
  * Define `X.page r := if 1 ≤ r then P (Int.toNat (r - 1)) else E`,
    `X.translation := τ`, and every `X.differential r := 0`.  The square-zero
    field is `zero_comp`.
  * For `X.nextIso r hr`, put `k := Int.toNat (r - 1)`.  Use
    `Int.toNat_of_nonneg`, `r = Int.ofNat (k + 1)`, and `omega` to reduce
    `X.page r` to `P k` and `X.page (r + 1)` to `P (k + 1)`.  After unfolding
    the recursion for `P`, the required isomorphism is `Iso.refl _`.
  * Package `X` with `starts_at_one := rfl`, `translation := fun r ↦ rfl`,
    and `page_one := ⟨Iso.refl E⟩`.  The argument uses `D` only to choose
    `S` and `T`, which is exactly all the present structure records; stronger
    association data would require strengthening the interface first.
  -/
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
      S.trans (shiftedEquivalenceIterate T (Int.toNat (r - 1))) := by
  simp [shiftedExactCoupleTranslation, hr]

end Formalization.Books.Homology.Unit21
