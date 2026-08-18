import Formalization.Books.Homology.Unit20.ExactCouples
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Differential objects

The unshifted definition in the source has no ambient shift functor, so it is
represented by the small source-facing category below.  For shifted objects,
the translation is bundled as a Mathlib category equivalence and the homology
object uses the canonical inverse-shift differential.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.3 Spectral sequences: differential objects -/

/-- An unshifted differential object `(A,d)` with `d² = 0`. -/
structure PlainDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] where
  carrier : C
  d : carrier ⟶ carrier
  d_squared : d ≫ d = 0

/-- A morphism of unshifted differential objects. -/
structure PlainDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] (A B : PlainDifferentialObject C) where
  hom : A.carrier ⟶ B.carrier
  comm : A.d ≫ hom = hom ≫ B.d

@[ext] theorem plainDifferentialObjectHom_ext {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {A B : PlainDifferentialObject C}
    {f g : PlainDifferentialObjectHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance plainDifferentialObjectCategory {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] : Category (PlainDifferentialObject C) where
  Hom A B := PlainDifferentialObjectHom A B
  id A := { hom := 𝟙 A.carrier, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc] }
  id_comp := by
    intro A B f
    apply plainDifferentialObjectHom_ext
    simp
  comp_id := by
    intro A B f
    apply plainDifferentialObjectHom_ext
    simp
  assoc := by
    intro A B D E f g h
    apply plainDifferentialObjectHom_ext
    simp [Category.assoc]

instance plainDifferentialObjectZeroMorphisms {C : Type u} [Category.{v} C]
    [Preadditive C] : HasZeroMorphisms (PlainDifferentialObject C) where
  zero := fun A B => ⟨{ hom := 0, comm := by simp }⟩
  comp_zero := by
    intro A B f D
    apply plainDifferentialObjectHom_ext
    change f.hom ≫ 0 = 0
    simp
  zero_comp := by
    intro A B D f
    apply plainDifferentialObjectHom_ext
    change 0 ≫ f.hom = 0
    simp

/-- The source's assertion that the category of differential objects is
abelian. -/
theorem plainDifferentialObject_abelian {C : Type u} [Category.{v} C]
    [Abelian C] : Nonempty (Abelian (PlainDifferentialObject C)) := by
  sorry

noncomputable instance plainDifferentialObjectAbelian {C : Type u} [Category.{v} C]
    [Abelian C] : Abelian (PlainDifferentialObject C) :=
  Classical.choice (plainDifferentialObject_abelian (C := C))

/-- The homology object `H(A,d) = Ker(d)/Im(d)`. -/
abbrev plainDifferentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : PlainDifferentialObject C) : C :=
  differentialHomology A.d A.d_squared

/-- A short exact sequence of differential objects. -/
structure PlainDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : PlainDifferentialObject C) where
  f : PlainDifferentialObjectHom A B
  g : PlainDifferentialObjectHom B D
  complex : f.hom ≫ g.hom = 0
  exact : (ShortComplex.mk f.hom g.hom complex).ShortExact

/-- A long exact sequence interface, indexed by the integers. -/
structure LongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (X : ℤ → C) where
  differential : ∀ n, X n ⟶ X (n + 1)
  complex : ∀ n, differential n ≫ differential (n + 1) = 0
  exact : ∀ n,
    (ShortComplex.mk (differential n) (differential (n + 1)) (complex n)).Exact

def differentialHomologyLongTerm {C : Type u} [Category.{v} C]
    [Abelian C] (A B D : PlainDifferentialObject C) (n : ℤ) : C :=
  if n % 3 = 0 then plainDifferentialHomology D
  else if n % 3 = 1 then plainDifferentialHomology A
  else plainDifferentialHomology B

theorem plainDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A B D : PlainDifferentialObject C}
    (S : PlainDifferentialShortExact A B D) :
    Nonempty (LongExactSequence (differentialHomologyLongTerm A B D)) := by
  sorry

/-! ### The injective self-map example -/

/-- An injective endomorphism of a differential object. -/
structure PlainDifferentialInjectiveEndomorphism {C : Type u} [Category.{v} C]
    [Abelian C] (A : PlainDifferentialObject C) where
  hom : PlainDifferentialObjectHom A A
  injective : Mono hom.hom

structure QuotientDifferentialMapData {C : Type u} [Category.{v} C]
    [Abelian C] {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) where
  differential : cokernel α.hom.hom ⟶ cokernel α.hom.hom
  square_zero : differential ≫ differential = 0
  induced : cokernel.π α.hom.hom ≫ differential =
    A.d ≫ cokernel.π α.hom.hom

theorem quotientDifferentialMap_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (QuotientDifferentialMapData α) := by
  sorry

noncomputable def quotientDifferentialMapData
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    QuotientDifferentialMapData α :=
  Classical.choice (quotientDifferentialMap_exists α)

noncomputable def quotientDifferentialMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    cokernel α.hom.hom ⟶ cokernel α.hom.hom :=
  (quotientDifferentialMapData α).differential

/-- The differential object `(A/alpha A,d)` from the self-map example. -/
def quotientDifferentialObject
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : PlainDifferentialObject C where
  carrier := cokernel α.hom.hom
  d := quotientDifferentialMap α
  d_squared := (quotientDifferentialMapData α).square_zero

def differentialSelfMapShortExact
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    PlainDifferentialShortExact A A (quotientDifferentialObject α) where
  f := α.hom
  g := { hom := cokernel.π α.hom.hom
         comm := (quotientDifferentialMapData α).induced.symm }
  complex := cokernel.condition _
  exact := by
    sorry

theorem differentialSelfMap_exactCouple_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α))) := by
  sorry

noncomputable def differentialSelfMapExactCouple
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    ExactCouple C (plainDifferentialHomology A)
      (plainDifferentialHomology (quotientDifferentialObject α)) :=
  Classical.choice (differentialSelfMap_exactCouple_exists α)

noncomputable def differentialSelfMapAssociatedSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : PlainSpectralSequence C 1 :=
  exactCoupleAssociatedSpectralSequence (differentialSelfMapExactCouple α)

theorem differentialSelfMap_E1
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (plainPageObject (differentialSelfMapAssociatedSpectralSequence α) 1 ≅
      plainDifferentialHomology (quotientDifferentialObject α)) := by
  sorry

/-- The separately numbered zeroth page in the self-map example. -/
abbrev differentialSelfMapE₀
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : C :=
  (quotientDifferentialObject α).carrier

abbrev differentialSelfMapD₀
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    differentialSelfMapE₀ α ⟶ differentialSelfMapE₀ α :=
  (quotientDifferentialObject α).d

theorem differentialSelfMap_starting_at_zero_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) :
    Nonempty (PlainSpectralSequence C 0) := by
  sorry

def selfMapAlphaPow {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) : ℕ →
      (A.carrier ⟶ A.carrier)
  | 0 => 𝟙 A.carrier
  | n + 1 => selfMapAlphaPow α n ≫ α.hom.hom

def selfMapBoundaryPreimage {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  if r = 0 then ⊥ else
    (Subobject.pullback (selfMapAlphaPow α (r - 1))).obj
      ((Subobject.«exists» A.d).obj ⊤)

def selfMapCyclePreimage {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  if r = 0 then ⊤ else
    (Subobject.pullback A.d).obj
      ((Subobject.«exists» (selfMapAlphaPow α r)).obj ⊤)

theorem selfMap_boundary_preimage_le_cycle_preimage
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundaryPreimage α r ≤ selfMapCyclePreimage α r := by
  sorry

def selfMapBoundaryPlus {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  letI : Mono α.hom.hom := α.injective
  selfMapBoundaryPreimage α r ⊔ Subobject.mk α.hom.hom

def selfMapCyclePlus {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject A.carrier :=
  letI : Mono α.hom.hom := α.injective
  selfMapCyclePreimage α r ⊔ Subobject.mk α.hom.hom

theorem selfMap_boundary_plus_le_cycle_plus
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundaryPlus α r ≤ selfMapCyclePlus α r := by
  exact sup_le_sup (selfMap_boundary_preimage_le_cycle_preimage α r) le_rfl

noncomputable def selfMapQuotientImageSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {X Q : C} (π : X ⟶ Q) (B : Subobject X) : Subobject Q :=
  Subobject.mk (Abelian.image.ι (B.arrow ≫ π))

def selfMapBoundarySubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapBoundaryPreimage α r)

def selfMapCycleSubobject {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Subobject (differentialSelfMapE₀ α) :=
  selfMapQuotientImageSubobject (cokernel.π α.hom.hom)
    (selfMapCyclePreimage α r)

theorem selfMap_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapBoundarySubobject α r ≤ selfMapCycleSubobject α r := by
  sorry

noncomputable def selfMapPageComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : C :=
  if r = 0 then differentialSelfMapE₀ α else
    subquotientObject (selfMapBoundaryPlus α r) (selfMapCyclePlus α r)
      (selfMap_boundary_plus_le_cycle_plus α r)

noncomputable def selfMapPageClassOfCycle
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ)
    {T : C} (z : T ⟶ (selfMapCyclePlus α r : C)) :
    T ⟶ selfMapPageComponent α r :=
  by
    by_cases hr : r = 0
    · subst r
      exact (z ≫ (selfMapCyclePlus α 0).arrow ≫ cokernel.π α.hom.hom) ≫
        eqToHom (by rfl)
    · exact (z ≫ cokernel.π (Subobject.ofLE (selfMapBoundaryPlus α r)
        (selfMapCyclePlus α r) (selfMap_boundary_plus_le_cycle_plus α r))) ≫
        eqToHom (by simp [selfMapPageComponent, hr, subquotientObject])

/-- The lift rule for the self-map spectral sequence, expressed on test-object
morphisms so it also makes sense in an arbitrary abelian category. -/
structure SelfMapPageDifferentialRule {C : Type u} [Category.{v} C]
    [Abelian C] {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) where
  differential : selfMapPageComponent α r ⟶ selfMapPageComponent α r
  differential_squared : differential ≫ differential = 0
  rule : ∀ {T : C}
    (z : T ⟶ (selfMapCyclePlus α r : C))
    (y : T ⟶ A.carrier)
    (yCycle : T ⟶ (selfMapCyclePlus α r : C))
    (_hy : yCycle ≫ (selfMapCyclePlus α r).arrow = y)
    (_h : z ≫ (selfMapCyclePlus α r).arrow ≫ A.d =
      y ≫ selfMapAlphaPow α r),
    selfMapPageClassOfCycle α r z ≫ differential =
      selfMapPageClassOfCycle α r yCycle

theorem selfMap_page_differential_rule_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    Nonempty (SelfMapPageDifferentialRule α r) := by
  sorry

/- The warning in the source is recorded as two named assertions rather than
silently adding either false inclusion as a hypothesis. -/
def selfMapAlphaSubobject
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (hα : Mono α.hom.hom) :
    Subobject A.carrier :=
  letI := hα
  Subobject.mk α.hom.hom

def selfMapWarningBoundaryInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : Prop :=
  selfMapAlphaSubobject α α.injective ≤ selfMapBoundaryPreimage α r

def selfMapWarningCycleInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) : Prop :=
  selfMapAlphaSubobject α α.injective ≤ selfMapCyclePreimage α r

theorem selfMap_page_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    {A : PlainDifferentialObject C}
    (α : PlainDifferentialInjectiveEndomorphism A) (r : ℕ) :
    selfMapPageComponent α r =
      if r = 0 then differentialSelfMapE₀ α else
        subquotientObject (selfMapBoundaryPlus α r)
          (selfMapCyclePlus α r) (selfMap_boundary_plus_le_cycle_plus α r) := rfl

/-! ### Shifted differential objects -/

/-- A differential object with differential `A ⟶ S A`. -/
structure ShiftedDifferentialObject (C : Type u) [Category.{v} C]
    [HasZeroMorphisms C] (S : C ≌ C) where
  carrier : C
  d : carrier ⟶ S.functor.obj carrier
  d_squared : d ≫ S.functor.map d = 0

/-- A morphism of shifted differential objects. -/
structure ShiftedDifferentialObjectHom {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    (A B : ShiftedDifferentialObject C S) where
  hom : A.carrier ⟶ B.carrier
  comm : A.d ≫ S.functor.map hom = hom ≫ B.d

@[ext] theorem shiftedDifferentialObjectHom_ext {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C}
    {A B : ShiftedDifferentialObject C S}
    {f g : ShiftedDifferentialObjectHom A B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance shiftedDifferentialObjectCategory {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {S : C ≌ C} :
    Category (ShiftedDifferentialObject C S) where
  Hom A B := ShiftedDifferentialObjectHom A B
  id A := { hom := 𝟙 A.carrier, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by
        rw [S.functor.map_comp, ← Category.assoc, f.comm, Category.assoc, g.comm,
          Category.assoc] }
  id_comp := by
    intro A B f
    apply shiftedDifferentialObjectHom_ext
    simp
  comp_id := by
    intro A B f
    apply shiftedDifferentialObjectHom_ext
    simp
  assoc := by
    intro A B D E f g h
    apply shiftedDifferentialObjectHom_ext
    simp [Category.assoc]

abbrev shiftedDifferentialHomology {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) : C :=
  translatedDifferentialHomology S A.d A.d_squared

def shiftedDifferentialObjectShift {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (A : ShiftedDifferentialObject C S) :
    ShiftedDifferentialObject C S where
  carrier := S.functor.obj A.carrier
  d := S.functor.map A.d
  d_squared := by
    rw [← S.functor.map_comp, A.d_squared, S.functor.map_zero]

theorem shiftedDifferentialHomology_shift_iso {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} (A : ShiftedDifferentialObject C S) :
    Nonempty (shiftedDifferentialHomology (shiftedDifferentialObjectShift S A) ≅
      S.functor.obj (shiftedDifferentialHomology A)) := by
  sorry

structure ShiftedDifferentialShortExact {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C}
    (A B D : ShiftedDifferentialObject C S) where
  f : ShiftedDifferentialObjectHom A B
  g : ShiftedDifferentialObjectHom B D
  complex : f.hom ≫ g.hom = 0
  exact : (ShortComplex.mk f.hom g.hom complex).ShortExact

structure ShiftedLongExactSequence {C : Type u} [Category.{v} C]
    [Abelian C] (S : C ≌ C) (X : ℤ → C) where
  differential : ∀ n, X n ⟶ X (n + 1)
  complex : ∀ n, differential n ≫ differential (n + 1) = 0
  exact : ∀ n,
    (ShortComplex.mk (differential n) (differential (n + 1)) (complex n)).Exact

theorem shiftedDifferentialShortExact_homology_long_exact
    {C : Type u} [Category.{v} C] [Abelian C] {S : C ≌ C}
    {A B D : ShiftedDifferentialObject C S}
    (Q : ShiftedDifferentialShortExact A B D) :
    ∃ X : ℤ → C, Nonempty (ShiftedLongExactSequence S X) := by
  sorry

theorem shiftedDifferentialObject_abelian {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} :
    Nonempty (Abelian (ShiftedDifferentialObject C S)) := by
  sorry

noncomputable instance shiftedDifferentialObjectAbelian {C : Type u} [Category.{v} C]
    [Abelian C] {S : C ≌ C} : Abelian (ShiftedDifferentialObject C S) :=
  Classical.choice (shiftedDifferentialObject_abelian (C := C) (S := S))

/- The shift-family variant in the source is represented by a commuting pair
of equivalences and a shifted injective self-map. -/
structure ShiftedSelfMapData (C : Type u) [Category.{v} C]
    [Abelian C] (S T : C ≌ C) where
  commute : T.functor ⋙ S.functor = S.functor ⋙ T.functor
  A : ShiftedDifferentialObject C S
  targetDifferential : T.inverse.obj A.carrier ⟶ S.functor.obj (T.inverse.obj A.carrier)
  target_d_squared : targetDifferential ≫ S.functor.map targetDifferential = 0
  alpha : ShiftedDifferentialObjectHom A
    { carrier := T.inverse.obj A.carrier
      d := targetDifferential
      d_squared := target_d_squared }
  injective : Mono alpha.hom
  quotientDifferential :
    cokernel alpha.hom ⟶ S.functor.obj (cokernel alpha.hom)
  quotient_d_squared :
    quotientDifferential ≫ S.functor.map quotientDifferential = 0
  quotient_induced :
    cokernel.π alpha.hom ≫ quotientDifferential =
      targetDifferential ≫ S.functor.map (cokernel.π alpha.hom)

def shiftedSelfMapQuotient {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    ShiftedDifferentialObject C S where
  carrier := cokernel D.alpha.hom
  d := D.quotientDifferential
  d_squared := D.quotient_d_squared

theorem shiftedSelfMap_exact_couple_exists {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    Nonempty (ShiftedExactCouple C (T.trans S) T
      (shiftedDifferentialHomology D.A)
      (S.inverse.obj (shiftedDifferentialHomology (shiftedSelfMapQuotient D)))) := by
  sorry

theorem shiftedSelfMap_spectral_sequence {C : Type u} [Category.{v} C]
    [Abelian C] {S T : C ≌ C} (D : ShiftedSelfMapData C S T) :
    ∃ X : TranslatedSpectralSequenceData C,
      X.r₀ = 1 ∧ Nonempty (X.page 1 ≅
        S.inverse.obj (shiftedDifferentialHomology (shiftedSelfMapQuotient D))) := by
  sorry

end Formalization.Books.Homology.Unit20
