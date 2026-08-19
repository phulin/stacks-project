import Formalization.Books.Homology.Unit20.FilteredDifferentialObjects
import Formalization.Books.Homology.Unit13.Complexes
import Formalization.Books.Homology.Unit11.KGroups
import Mathlib.Algebra.Homology.Additive

/-!
# Filtered complexes

Filtered complexes are complexes in the filtered-object category from
Chapter 19.  The terms of the associated spectral sequence are recorded by
the categorical subquotients of the filtration steps; the bidegrees use the
source convention `(p,q)` with total degree `p + q`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit16
open Formalization.Books.Homology.Unit13
open Formalization.Books.Homology.Unit11
open scoped BigOperators

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.5 Filtered complexes -/

/-- A filtered cochain complex. -/
abbrev FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  CochainComplex (FilteredObject C) ℤ

abbrev filteredComplexTerm {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) : FilteredObject C :=
  K.X n

def filteredComplexDifferential {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) :
    (K.X n).carrier ⟶ (K.X (n + 1)).carrier :=
  FilteredHom.hom (K.d n (n + 1))

def filteredComplexGradedPiece {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  letI : (gradedPieceFunctor (C := C) p).Additive :=
    gradedPieceFunctor_is_additive p
  ((gradedPieceFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

abbrev filteredComplexE₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  gradedPiece (K.X (p + q)) p

def filteredComplexD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₀ K p q ⟶ filteredComplexE₀ K p (q + 1) :=
  gradedPieceMap (C := C) (K.d (p + q) (p + q + 1)) p ≫
    eqToHom (by
      congr 2
      ring)

def filteredComplexE₁ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)).obj
    (filteredComplexGradedPiece K p)

theorem filteredComplex_E₀_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Nonempty (filteredComplexE₀ K p q ≅ gradedPiece (K.X (p + q)) p) := by
  sorry

theorem filteredComplex_E₁_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₁ K p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)).obj
        (filteredComplexGradedPiece K p) := rfl

/-! ### `Zᵣ`, `Bᵣ`, and the bidegree of `dᵣ` -/

def filteredComplexCycleCore {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (Subobject.pullback (filteredComplexDifferential K (p + q))).obj
      ((K.X (p + q + 1)).filtration.obj (p + r)) ⊓
    (K.X (p + q)).filtration.obj p

def filteredComplexBoundaryCore {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (Subobject.«exists» (FilteredHom.hom (K.d (p + q - 1) (p + q)))).obj
      ((K.X (p + q - 1)).filtration.obj (p - r + 1)) ⊓
    (K.X (p + q)).filtration.obj p

def filteredComplexCyclePlus {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  filteredComplexCycleCore K r p q ⊔ (K.X (p + q)).filtration.obj (p + 1)

def filteredComplexBoundaryPlus {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  filteredComplexBoundaryCore K r p q ⊔ (K.X (p + q)).filtration.obj (p + 1)

theorem filteredComplex_boundary_le_cycle
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexBoundaryPlus K r p q ≤ filteredComplexCyclePlus K r p q := by
  sorry

noncomputable def filteredComplexPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject (filteredComplexBoundaryPlus K r p q)
    (filteredComplexCyclePlus K r p q)
    (filteredComplex_boundary_le_cycle K r p q)

noncomputable def filteredComplexPageClass {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K r p q : C)) :
    T ⟶ filteredComplexPage K r p q :=
  z ≫ cokernel.π (Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
    (filteredComplexCyclePlus K r p q)
    (filteredComplex_boundary_le_cycle K r p q))

structure FilteredComplexPageDifferentials {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  differential : ∀ (r : ℕ) (p q : ℤ),
    filteredComplexPage K (r : ℤ) p q ⟶
      filteredComplexPage K (r : ℤ) (p + r) (q - r + 1)
  square_zero : ∀ (r : ℕ) (p q : ℤ),
    differential r p q ≫ differential r (p + r) (q - r + 1) = 0
  lift_rule : ∀ (r : ℕ) (p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K (r : ℤ) p q : C))
    (zNext : T ⟶ (filteredComplexCyclePlus K (r : ℤ) (p + r) (q - r + 1) : C))
    (_hz : zNext ≫ (filteredComplexCyclePlus K (r : ℤ) (p + r) (q - r + 1)).arrow =
      z ≫ (filteredComplexCyclePlus K (r : ℤ) p q).arrow ≫
        filteredComplexDifferential K (p + q) ≫
          eqToHom (congrArg (fun n : ℤ => (K.X n).carrier) (by omega))),
    filteredComplexPageClass K (r : ℤ) p q z ≫ differential r p q =
      filteredComplexPageClass K (r : ℤ) (p + r) (q - r + 1) zNext

theorem filteredComplex_page_differentials_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexPageDifferentials K) := by
  sorry

def bigradedShift {C : Type u} [Category.{v} C] (a b : ℤ) :
    GradedObject (ℤ × ℤ) C ⥤ GradedObject (ℤ × ℤ) C :=
  GradedObject.comap C (fun x => (a + x.1, b + x.2))

structure FilteredComplexSpectralSequence {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  page : ℕ → GradedObject (ℤ × ℤ) C
  differential : ∀ r : ℕ,
    page r ⟶ (bigradedShift r (-r + 1)).obj (page r)
  square_zero : ∀ r : ℕ,
    differential r ≫ (bigradedShift r (-r + 1)).map (differential r) = 0
  next_page : ∀ (r : ℕ) (p q : ℤ), Nonempty
    (page (r + 1) (p, q) ≅
      subquotientObject
        (Subobject.mk (Abelian.image.ι
          (differential r (p - r, q + r - 1) ≫
            (eqToHom (by
              change page r
                (r + (p - r), (-r + 1) + (q + r - 1)) = page r (p, q)
              congr 1; ring) :
              (bigradedShift r (-r + 1)).obj (page r)
                  (p - r, q + r - 1) ⟶ page r (p, q)))))
        (Subobject.mk (kernel.ι (differential r (p, q))))
        (by sorry))
  component_iso : ∀ (r : ℕ) (p q : ℤ),
    Nonempty (page r (p, q) ≅ filteredComplexPage K r p q)
  zero_page : ∀ p q : ℤ, Nonempty (page 0 (p, q) ≅ filteredComplexE₀ K p q)
  first_page : ∀ p q : ℤ, Nonempty (page 1 (p, q) ≅ filteredComplexE₁ K p q)

theorem filteredComplex_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexSpectralSequence K) := by
  sorry

/-! ### The `d₁` boundary and functoriality -/

noncomputable def filteredComplexStepFunctor
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    FilteredObject C ⥤ C where
  obj A := filtrationStep A p
  map f := filtrationStepMap f p
  map_id := by
    intro A
    apply (cancel_mono (A.filtration.obj p).arrow).1
    simp only [filtrationStep, filtrationStepMap, Subobject.factorThru_arrow,
      filteredHom_id_hom]
    rw [Category.comp_id, Category.id_comp]
  map_comp := by
    intro A B D f g
    apply (cancel_mono (D.filtration.obj p).arrow).1
    simp only [filtrationStepMap, filtrationStep, filteredHom_comp_hom]
    have h := Subobject.factors_of_factors_right
      ((B.filtration.obj p).factorThru
        ((A.filtration.obj p).arrow ≫ FilteredHom.hom f)
        (f.map_filtration p))
      (g := (B.filtration.obj p).arrow ≫ FilteredHom.hom g) (g.map_filtration p)
    rw [← Category.assoc, Subobject.factorThru_arrow] at h
    simpa only [Category.assoc] using h

instance filteredComplexStepFunctor_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [Abelian C] (p : ℤ) :
    (filteredComplexStepFunctor (C := C) p).PreservesZeroMorphisms where
  map_zero _A _B := by
    apply (cancel_mono (_B.filtration.obj p).arrow).1
    simp only [filteredComplexStepFunctor, filtrationStepMap, filtrationStep,
      Subobject.factorThru_arrow]
    change
      (_A.filtration.obj p).arrow ≫ (0 : _A.carrier ⟶ _B.carrier) =
        (0 : (_A.filtration.obj p : C) ⟶ (_B.filtration.obj p : C)) ≫
          (_B.filtration.obj p).arrow
    simp

noncomputable def filteredComplexStepComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  ((filteredComplexStepFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

noncomputable def filteredComplexStepInclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) (hpq : p ≤ q) :
    filteredComplexStepComplex K q ⟶ filteredComplexStepComplex K p := by
  refine { f := fun n => ?_, comm' := ?_ }
  · exact Subobject.ofLE ((K.X n).filtration.obj q)
      ((K.X n).filtration.obj p) ((K.X n).filtration.antitone hpq)
  intro n m hnm
  sorry

noncomputable def filteredComplexD1Middle
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ where
  X n := cokernel ((filteredComplexStepInclusion K p (p + 2) (by omega)).f n)
  d n m := cokernel.desc
    ((filteredComplexStepInclusion K p (p + 2) (by omega)).f n)
    ((filteredComplexStepComplex K p).d n m ≫
      cokernel.π ((filteredComplexStepInclusion K p (p + 2) (by omega)).f m)) (by
        sorry)
  shape n m hnm := by
    sorry
  d_comp_d' n m k hnm hmk := by
    sorry

noncomputable def filteredComplexD1Inclusion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    filteredComplexGradedPiece K (p + 1) ⟶ filteredComplexD1Middle K p := by
  refine { f := fun n => ?_, comm' := ?_ }
  · change cokernel _ ⟶ cokernel _
    refine cokernel.desc _
      (Subobject.ofLE ((K.X n).filtration.obj (p + 1))
        ((K.X n).filtration.obj p)
        ((K.X n).filtration.antitone (by omega)) ≫
        cokernel.π ((filteredComplexStepInclusion K p (p + 2) (by omega)).f n)) ?_
    sorry
  · intro n m hnm
    sorry

noncomputable def filteredComplexD1Projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    filteredComplexD1Middle K p ⟶ filteredComplexGradedPiece K p := by
  refine { f := fun n => ?_, comm' := ?_ }
  · change cokernel _ ⟶ cokernel _
    refine cokernel.desc _ (cokernel.π _) ?_
    sorry
  · intro n m hnm
    sorry

theorem filteredComplexD1_inclusion_projection
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    filteredComplexD1Inclusion K p ≫ filteredComplexD1Projection K p = 0 := by
  sorry

def filteredComplexD1ShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (filteredComplexD1Inclusion K p)
    (filteredComplexD1Projection K p)
    (filteredComplexD1_inclusion_projection K p)

theorem filteredComplexD1_boundary_description
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    (filteredComplexD1ShortExact K p).ShortExact :=
  by
    sorry

def FilteredComplexRaisesFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ (n p : ℤ),
    (K.X n).filtration.obj p ≤
      (Subobject.pullback (filteredComplexDifferential K n)).obj
        ((K.X (n + 1)).filtration.obj (p + 1))

theorem filteredComplexRaisesFiltration_zero_graded_differential
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexRaisesFiltration K) (p : ℤ) :
    ∀ q : ℤ, filteredComplexD₀ K p q = 0 := by
  sorry

structure FilteredComplexSpectralSequenceHom {C : Type u}
    [Category.{v} C] [Abelian C] {K L : FilteredComplex C}
    (Sₖ : FilteredComplexSpectralSequence K)
    (Sₗ : FilteredComplexSpectralSequence L) where
  pageHom : ∀ r : ℕ, Sₖ.page r ⟶ Sₗ.page r
  compatible : ∀ r : ℕ,
    pageHom r ≫ Sₗ.differential r =
      Sₖ.differential r ≫ (bigradedShift r (-r + 1)).map (pageHom r)

theorem filteredComplex_functoriality
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) :
    ∀ (Sₖ : FilteredComplexSpectralSequence K)
      (Sₗ : FilteredComplexSpectralSequence L),
      Nonempty (FilteredComplexSpectralSequenceHom Sₖ Sₗ) := by
  sorry

/-! ### Cohomology filtrations and limits -/

def filteredComplexForgetful {C : Type u} [Category.{v} C] [Abelian C] :
    FilteredObject C ⥤ C where
  obj A := A.carrier
  map f := f.hom
  map_id _A := rfl
  map_comp _f _g := rfl

instance filteredComplexForgetful_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] [Abelian C] :
    (filteredComplexForgetful (C := C)).PreservesZeroMorphisms where
  map_zero _A _B := rfl

noncomputable def filteredComplexUnderlying {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : CochainComplex C ℤ :=
  ((filteredComplexForgetful (C := C)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

abbrev filteredComplexCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj
    (filteredComplexUnderlying K)

noncomputable def filteredComplexStepToUnderlying
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    filteredComplexStepComplex K p ⟶ filteredComplexUnderlying K := by
  refine { f := fun n => ((K.X n).filtration.obj p).arrow, comm' := ?_ }
  intro n m hnm
  sorry

abbrev filteredComplexStepCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).obj
    (filteredComplexStepComplex K p)

noncomputable def filteredComplexStepCohomologyMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    filteredComplexStepCohomology K n p ⟶ filteredComplexCohomology K n :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map
    (filteredComplexStepToUnderlying K p)

noncomputable def filteredComplexCohomologyFiltrationStep
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    Subobject (filteredComplexCohomology K n) :=
  Subobject.mk (Abelian.image.ι (filteredComplexStepCohomologyMap K n p))

theorem filteredComplexCohomologyFiltration_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    Nonempty (DecreasingFiltration C (filteredComplexCohomology K n)) := by
  sorry

noncomputable def filteredComplexCohomologyFiltration
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    DecreasingFiltration C (filteredComplexCohomology K n) where
  obj p := filteredComplexCohomologyFiltrationStep K n p
  antitone := by
    intro p q hpq
    sorry

def filteredComplexCohomologyFilteredObject
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    FilteredObject C where
  carrier := filteredComplexCohomology K n
  filtration := filteredComplexCohomologyFiltration K n

theorem filteredComplexCohomology_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    (filteredComplexCohomologyFilteredObject K n).filtration.obj p =
      filteredComplexCohomologyFiltrationStep K n p := rfl

theorem filteredComplexCohomology_graded_formula
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    Nonempty
      (gradedPiece (filteredComplexCohomologyFilteredObject K n) p ≅
        subquotientObject
          ((filteredComplexCohomologyFilteredObject K n).filtration.obj (p + 1))
          ((filteredComplexCohomologyFilteredObject K n).filtration.obj p)
          ((filteredComplexCohomologyFilteredObject K n).filtration.antitone (by omega))) := by
  sorry

noncomputable def filteredComplexCohomologyQuotientSystem
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) : ℤᵒᵖ ⥤ C where
  obj p := cokernel ((filteredComplexCohomologyFilteredObject K n).filtration.obj
    (Opposite.unop p)).arrow
  map := fun {p q} f => by
    refine cokernel.desc
      ((filteredComplexCohomologyFilteredObject K n).filtration.obj
        (Opposite.unop p)).arrow
      (cokernel.π ((filteredComplexCohomologyFilteredObject K n).filtration.obj
        (Opposite.unop q)).arrow) ?_
    have h : Opposite.unop q ≤ Opposite.unop p := by
      exact leOfHom f.unop
    rw [← Subobject.ofLE_arrow
      ((filteredComplexCohomologyFilteredObject K n).filtration.antitone h)]
    rw [Category.assoc, cokernel.condition, comp_zero]
  map_id := by
    intro p
    sorry
  map_comp := by
    intro p q r f g
    sorry

structure FilteredComplexCohomologyCompletion
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) where
  cone : Cone (filteredComplexCohomologyQuotientSystem K n)
  isLimit : IsLimit cone
  completionIso : Nonempty
    (filteredComplexCohomology K n ≅ cone.pt)

def FilteredComplexCohomologyComplete
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, Nonempty (FilteredComplexCohomologyCompletion K n)

structure FilteredComplexLimitData {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  Binf : ∀ (p q : ℤ), Subobject (K.X (p + q)).carrier
  Zinf : ∀ (p q : ℤ), Subobject (K.X (p + q)).carrier
  Binf_spec : ∀ p q (r : ℕ),
    filteredComplexBoundaryPlus K (r : ℤ) p q ≤ Binf p q
  Binf_least : ∀ p q Y,
    (∀ (r : ℕ), filteredComplexBoundaryPlus K (r : ℤ) p q ≤ Y) → Binf p q ≤ Y
  Zinf_spec : ∀ p q (r : ℕ),
    Zinf p q ≤ filteredComplexCyclePlus K (r : ℤ) p q
  Zinf_greatest : ∀ p q Y,
    (∀ (r : ℕ), Y ≤ filteredComplexCyclePlus K (r : ℤ) p q) → Y ≤ Zinf p q
  Binf_le_Zinf : ∀ p q, Binf p q ≤ Zinf p q

noncomputable def filteredComplexLimitPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (L : FilteredComplexLimitData K)
    (p q : ℤ) : C :=
  subquotientObject (L.Binf p q) (L.Zinf p q) (L.Binf_le_Zinf p q)

def filteredComplexLimit_graded_subquotient
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    IsSubquotientOf
      (X := gradedPiece (filteredComplexCohomologyFilteredObject K (p + q)) p)
      (Y := filteredComplexLimitPage K L p q)

def filteredComplexLimit_graded_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    Nonempty
      (gradedPiece (filteredComplexCohomologyFilteredObject K (p + q)) p ≅
        filteredComplexLimitPage K L p q)

/-! ### Regularity, boundedness, and convergence -/

def filteredComplexRegular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p, q) = 0

def filteredComplexCoregular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p - r, q + r - 1) = 0

def filteredComplexBounded {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, Set.Finite {p : ℤ | ¬ IsZero (S.page 0 (p, n - p))}

def filteredComplexBoundedBelow {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero (S.page 0 (p, n - p))

def filteredComplexBoundedAbove {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, p ≤ b → IsZero (S.page 0 (p, n - p))

theorem filteredComplex_regular_iff_stable_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexRegular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexCyclePlus K (r : ℤ) p q =
          filteredComplexCyclePlus K (r + 1 : ℤ) p q := by
  sorry

theorem filteredComplex_coregular_iff_stable_boundaries
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexCoregular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexBoundaryPlus K (r : ℤ) p q =
          filteredComplexBoundaryPlus K (r + 1 : ℤ) p q := by
  sorry

theorem filteredComplex_bounded_iff_below_and_above
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBounded S ↔ filteredComplexBoundedBelow S ∧
      filteredComplexBoundedAbove S := by
  sorry

theorem filteredComplex_bounded_below_regular
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBoundedBelow S → filteredComplexRegular S := by
  sorry

theorem filteredComplex_bounded_above_coregular
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBoundedAbove S → filteredComplexCoregular S := by
  sorry

def filteredComplexWeaklyConverges {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∃ L : FilteredComplexLimitData K, filteredComplexLimit_graded_iso K L

def filteredComplexAbuts {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  filteredComplexWeaklyConverges K ∧
    ∀ n : ℤ, ∃ hF : HasIntersection (filteredComplexCohomologyFilteredObject K n).filtration,
      ∃ hU : HasUnion (filteredComplexCohomologyFilteredObject K n).filtration,
        intersection hF = ⊥ ∧ union hU = ⊤

def filteredComplexConverges {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  filteredComplexAbuts K ∧ ∃ S : FilteredComplexSpectralSequence K,
    filteredComplexRegular S ∧ FilteredComplexCohomologyComplete K

theorem filteredComplex_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    filteredComplexWeaklyConverges K ↔
      ∃ L : FilteredComplexLimitData K, filteredComplexLimit_graded_iso K L := by
  sorry

theorem filteredComplex_abutment_iff
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    filteredComplexAbuts K ↔
      filteredComplexWeaklyConverges K ∧
        ∀ n : ℤ, ∃ hF : HasIntersection (filteredComplexCohomologyFilteredObject K n).filtration,
          ∃ hU : HasUnion (filteredComplexCohomologyFilteredObject K n).filtration,
            intersection hF = ⊥ ∧ union hU = ⊤ := by
  sorry

theorem filteredComplex_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    filteredComplexConverges K ↔
      filteredComplexAbuts K ∧ ∃ S : FilteredComplexSpectralSequence K,
        filteredComplexRegular S ∧ FilteredComplexCohomologyComplete K := by
  sorry

/-! ### Finite filtrations, Euler characteristics, and the trivial criterion -/

def FilteredComplexFiniteFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

theorem filteredComplex_finite_filtration_converges
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K) :
    filteredComplexWeaklyConverges K ∧ filteredComplexAbuts K := by
  sorry

theorem filteredComplex_finite_filtration_converges_to_cohomology
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K) :
    filteredComplexConverges K := by
  sorry

/- The weak-Serre conclusion is part of the finite-filtration result in the
   source: membership of one page in a weak Serre class propagates through
   the finite filtration on each cohomology object. -/
theorem filteredComplex_finite_filtration_weak_serre
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ, P (S.page r (p, q))) :
    ∀ n : ℤ, P (filteredComplexCohomology K n) := by
  sorry

def filteredComplexAlternatingSign (n : ℤ) : ℤ :=
  if n % 2 = 0 then 1 else -1

structure FilteredComplexK0AlternatingSumStatement {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass] where
  finite_cohomology : Set.Finite {n : ℤ | ¬ IsZero (filteredComplexCohomology K n)}
  finite_page : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}
  page_mem : ∀ p q : ℤ, P (S.page r (p, q))
  cohomology_mem : ∀ n : ℤ, P (filteredComplexCohomology K n)
  alternating_relation : ∃ s : Finset ℤ, ∃ t : Finset (ℤ × ℤ),
    (∀ n : ℤ, ¬ IsZero (filteredComplexCohomology K n) → n ∈ s) ∧
      (∀ pq : ℤ × ℤ, ¬ IsZero (S.page r pq) → pq ∈ t) ∧
      (Finset.sum s (fun n =>
          filteredComplexAlternatingSign n •
            KZero.classOf (⟨filteredComplexCohomology K n, cohomology_mem n⟩ :
              P.FullSubcategory))) =
        Finset.sum t (fun pq =>
          filteredComplexAlternatingSign (pq.1 + pq.2) •
            KZero.classOf (⟨S.page r pq, page_mem pq.1 pq.2⟩ : P.FullSubcategory))

theorem filteredComplex_K0_alternating_sum
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ, P (S.page r (p, q)))
    (hS : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}) :
    Nonempty (FilteredComplexK0AlternatingSumStatement K S r P) := by
  sorry

structure FilteredComplexTrivialConvergenceHypotheses {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  high_zero : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
    IsZero (filteredComplexStepCohomology K n p)
  low_iso : ∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
    IsIso (filteredComplexStepCohomologyMap K n p)

theorem filteredComplex_trivial_convergence
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexTrivialConvergenceHypotheses K) :
    ∃ S : FilteredComplexSpectralSequence K,
      filteredComplexBounded S ∧
      (∀ n : ℤ, (filteredComplexCohomologyFilteredObject K n).IsFinite) ∧
      filteredComplexConverges K := by
  sorry

end Formalization.Books.Homology.Unit20
