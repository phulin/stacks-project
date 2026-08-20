import Formalization.Books.Homology.Unit20.FilteredComplexes

/-!
# Homological Algebra, Chapter 24: Spectral sequences: filtered complexes

This file gives the source-facing interface for a filtered cochain complex.
The filtered-object, subobject, cohomology, and categorical quotient
constructions are inherited from the preceding chapters.  The associated
graded complex remains unshifted; the source's `(p, q)` convention is
implemented by evaluating degree `p + q`.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit20
open Formalization.Books.Homology.Unit13
open Formalization.Books.Homology.Unit11
open scoped BigOperators

universe v u

namespace Formalization.Books.Homology.Unit24

/-! ## Filtered complexes and their first pages -/

/-- A filtered complex is a cochain complex in the category of filtered
objects.  This is the canonical filtered-object definition from Chapter 20.
-/
abbrev FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Homology.Unit20.FilteredComplex C

abbrev filteredComplexTerm {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) : FilteredObject C := K.X n

def filteredComplexDifferential {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n : ℤ) :
    (K.X n).carrier ⟶ (K.X (n + 1)).carrier :=
  FilteredHom.hom (K.d n (n + 1))

/- The filtration step is itself a cochain complex.  This is the canonical
   construction from the preceding chapter, and records the source's
   observation that every `F^p K` is a complex. -/
abbrev filteredComplexFiltrationStep {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexStepComplex K p

/-! The canonical associated-graded complex is kept unshifted: its degree
`n` term is `gr^p K^n`.  The source's complementary degree is accounted for
by evaluating it at `n = p + q`. -/
abbrev filteredComplexGradedPiece {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexGradedPiece K p

abbrev filteredComplexE₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexE₀ K p q

abbrev filteredComplexD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₀ K p q ⟶ filteredComplexE₀ K p (q + 1) :=
  Formalization.Books.Homology.Unit20.filteredComplexD₀ K p q

def filteredComplexSourceD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) :
    gradedPiece (K.X (p + q)) p ⟶ gradedPiece (K.X (p + q + 1)) p :=
  gradedPieceMap (K.d (p + q) (p + q + 1)) p

abbrev filteredComplexE₁ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p q : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexE₁ K p q

theorem filteredComplex_E₀_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₀ K p q = gradedPiece (K.X (p + q)) p := rfl

theorem filteredComplex_D₀_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexD₀ K p q =
      filteredComplexSourceD₀ K p q ≫
        eqToHom (congrArg (fun n : ℤ => gradedPiece (K.X n) p) (by omega)) := by
  rfl

theorem filteredComplex_E₁_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    filteredComplexE₁ K p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)).obj
        (filteredComplexGradedPiece K p) := rfl

abbrev filteredComplexUnshiftedGradedPiece {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexGradedPiece K p

theorem filteredComplex_E₁_source_formula {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Nonempty (filteredComplexE₁ K p q ≅
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (p + q)).obj
        (filteredComplexUnshiftedGradedPiece K p)) := by
  exact ⟨Iso.refl _⟩

/-! The countable-direct-sum warning and the temporary hypothesis used in the
direct-sum construction.  The general construction below does not require
this hypothesis. -/

abbrev CountableDirectSumsExact (C : Type u) [Category.{v} C]
    [Abelian C] [HasCountableCoproducts C] : Prop :=
  Formalization.Books.Homology.Unit20.CountableDirectSumsExact C

abbrev NonExactCountableDirectSumsExample :=
  Formalization.Books.Homology.Unit16.NonExactGradedTotalExample

theorem exists_nonExactCountableDirectSumsExample :
    Nonempty (NonExactCountableDirectSumsExample.{u}) := by
  exact Formalization.Books.Homology.Unit16.exists_nonExactGradedTotalExample

/-! ### `Zᵣ`, `Bᵣ`, pages, and page differentials

The displayed Z/B quotients represent pages with index `r ≥ 1`; page `0`
is the associated graded object and is handled separately below. -/

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
  exact Formalization.Books.Homology.Unit20.filteredComplex_boundary_le_cycle K r p q

theorem filteredComplex_boundary_monotone
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexBoundaryPlus K r p q ≤
      filteredComplexBoundaryPlus K (r + 1) p q := by
  change Formalization.Books.Homology.Unit20.filteredComplexBoundaryPlus K r p q ≤
    Formalization.Books.Homology.Unit20.filteredComplexBoundaryPlus K (r + 1) p q
  apply sup_le_sup_right
  apply inf_le_inf_right
  apply (Subobject.exists _).monotone
  apply (K.X (p + q - 1)).filtration.antitone
  omega

theorem filteredComplex_cycle_antitone
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (r p q : ℤ) :
    filteredComplexCyclePlus K (r + 1) p q ≤
      filteredComplexCyclePlus K r p q := by
  change (filteredComplexCycleCore K (r + 1) p q ⊔
      (K.X (p + q)).filtration.obj (p + 1)) ≤
    (filteredComplexCycleCore K r p q ⊔
      (K.X (p + q)).filtration.obj (p + 1))
  apply sup_le_sup_right
  apply inf_le_inf_right
  apply (Subobject.pullback _).monotone
  apply (K.X (p + q + 1)).filtration.antitone
  omega

/-- The source's `Zᵣ^{p,q}` and `Bᵣ^{p,q}` as categorical subquotients of
`K^(p+q)`. -/
noncomputable def filteredComplexZ {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject ((K.X (p + q)).filtration.obj (p + 1))
    (filteredComplexCyclePlus K r p q)
    (le_sup_right)

noncomputable def filteredComplexB {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (r p q : ℤ) : C :=
  subquotientObject ((K.X (p + q)).filtration.obj (p + 1))
    (filteredComplexBoundaryPlus K r p q)
    (le_sup_right)

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

structure FilteredComplexPageSubobjectData {C : Type u}
    [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) where
  B : Subobject (filteredComplexE₀ K p q)
  Z : Subobject (filteredComplexE₀ K p q)
  B_le_Z : B ≤ Z
  B_component : Nonempty ((B : C) ≅ filteredComplexB K r p q)
  Z_component : Nonempty ((Z : C) ≅ filteredComplexZ K r p q)

theorem filteredComplex_page_subobjects_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r p q : ℤ) :
    Nonempty (FilteredComplexPageSubobjectData K r p q) := by
  let hF10 : (K.X (p + q)).filtration.obj (p + 1) ≤
      (K.X (p + q)).filtration.obj p :=
    (K.X (p + q)).filtration.antitone (by omega)
  let hB1 : (K.X (p + q)).filtration.obj (p + 1) ≤
      filteredComplexBoundaryPlus K r p q := le_sup_right
  let hZ1 : (K.X (p + q)).filtration.obj (p + 1) ≤
      filteredComplexCyclePlus K r p q := le_sup_right
  let hB0 : filteredComplexBoundaryPlus K r p q ≤
      (K.X (p + q)).filtration.obj p := by
    apply sup_le
    · exact inf_le_right
    · exact (K.X (p + q)).filtration.antitone (by omega)
  let hZ0 : filteredComplexCyclePlus K r p q ≤
      (K.X (p + q)).filtration.obj p := by
    apply sup_le
    · exact inf_le_right
    · exact (K.X (p + q)).filtration.antitone (by omega)
  let bObj : C := cokernel (Subobject.ofLE
      ((K.X (p + q)).filtration.obj (p + 1))
      (filteredComplexBoundaryPlus K r p q) hB1)
  let zObj : C := cokernel (Subobject.ofLE
      ((K.X (p + q)).filtration.obj (p + 1))
      (filteredComplexCyclePlus K r p q) hZ1)
  let bMap : bObj ⟶ filteredComplexE₀ K p q :=
    cokernel.map
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        (filteredComplexBoundaryPlus K r p q) hB1)
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        ((K.X (p + q)).filtration.obj p) hF10)
      (𝟙 ((K.X (p + q)).filtration.obj (p + 1) : C))
      (Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
        ((K.X (p + q)).filtration.obj p) hB0)
      (by
        simpa only [Category.id_comp] using
          (Subobject.ofLE_comp_ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexBoundaryPlus K r p q)
            ((K.X (p + q)).filtration.obj p)
            hB1 hB0))
  have hbMap_mono : Mono bMap := by
    apply Abelian.mono_cokernel_map_of_isPullback
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by
      simpa only [Category.id_comp] using
        (Subobject.ofLE_comp_ofLE
          ((K.X (p + q)).filtration.obj (p + 1))
          (filteredComplexBoundaryPlus K r p q)
          ((K.X (p + q)).filtration.obj p)
          le_sup_right hB0)⟩
  let : Mono bMap := hbMap_mono
  let zMap : zObj ⟶ filteredComplexE₀ K p q :=
    cokernel.map
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        (filteredComplexCyclePlus K r p q) hZ1)
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        ((K.X (p + q)).filtration.obj p) hF10)
      (𝟙 ((K.X (p + q)).filtration.obj (p + 1) : C))
      (Subobject.ofLE (filteredComplexCyclePlus K r p q)
        ((K.X (p + q)).filtration.obj p) hZ0)
      (by
        simpa only [Category.id_comp] using
          (Subobject.ofLE_comp_ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexCyclePlus K r p q)
            ((K.X (p + q)).filtration.obj p)
            hZ1 hZ0))
  have hzMap_mono : Mono zMap := by
    apply Abelian.mono_cokernel_map_of_isPullback
    apply IsPullback.of_vert_isIso_mono
    exact ⟨by
      simpa only [Category.id_comp] using
        (Subobject.ofLE_comp_ofLE
          ((K.X (p + q)).filtration.obj (p + 1))
          (filteredComplexCyclePlus K r p q)
          ((K.X (p + q)).filtration.obj p)
          le_sup_right hZ0)⟩
  let : Mono zMap := hzMap_mono
  let bzMap : bObj ⟶ zObj :=
    cokernel.map
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        (filteredComplexBoundaryPlus K r p q) hB1)
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        (filteredComplexCyclePlus K r p q) hZ1)
      (𝟙 ((K.X (p + q)).filtration.obj (p + 1) : C))
      (Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
        (filteredComplexCyclePlus K r p q)
        (filteredComplex_boundary_le_cycle K r p q))
      (by
        simpa only [Category.id_comp] using
          (Subobject.ofLE_comp_ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexBoundaryPlus K r p q)
            (filteredComplexCyclePlus K r p q)
            hB1 (filteredComplex_boundary_le_cycle K r p q)))
  have hBZ : Subobject.mk bMap ≤ Subobject.mk zMap := by
    apply Subobject.mk_le_mk_of_comm bzMap
    apply (cancel_epi (cokernel.π
      (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
        (filteredComplexBoundaryPlus K r p q) hB1))).1
    have hbzπ : cokernel.π
          (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexBoundaryPlus K r p q) hB1) ≫ bzMap =
        Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
          (filteredComplexCyclePlus K r p q)
          (filteredComplex_boundary_le_cycle K r p q) ≫
          cokernel.π (Subobject.ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexCyclePlus K r p q) hZ1) := by
      dsimp [bObj, zObj, bzMap]
      exact cokernel.π_desc _ _ _
    have hzπ : cokernel.π
          (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexCyclePlus K r p q) hZ1) ≫ zMap =
        Subobject.ofLE (filteredComplexCyclePlus K r p q)
          ((K.X (p + q)).filtration.obj p) hZ0 ≫
          cokernel.π (Subobject.ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            ((K.X (p + q)).filtration.obj p) hF10) := by
      dsimp [bObj, zObj, filteredComplexE₀, zMap]
      exact cokernel.π_desc _ _ _
    have hbπ : cokernel.π
          (Subobject.ofLE ((K.X (p + q)).filtration.obj (p + 1))
            (filteredComplexBoundaryPlus K r p q) hB1) ≫ bMap =
        Subobject.ofLE (filteredComplexBoundaryPlus K r p q)
          ((K.X (p + q)).filtration.obj p) hB0 ≫
          cokernel.π (Subobject.ofLE
            ((K.X (p + q)).filtration.obj (p + 1))
            ((K.X (p + q)).filtration.obj p) hF10) := by
      dsimp [bObj, filteredComplexE₀, bMap]
      exact cokernel.π_desc _ _ _
    rw [← Category.assoc, hbzπ, Category.assoc, hzπ, hbπ]
    simpa only [filteredComplexE₀,
      Formalization.Books.Homology.Unit20.filteredComplexE₀,
      Formalization.Books.Homology.Unit19.gradedPiece, Category.assoc] using
      congrArg (fun f => f ≫ cokernel.π (Subobject.ofLE
        ((K.X (p + q)).filtration.obj (p + 1))
        ((K.X (p + q)).filtration.obj p) hF10))
        (Subobject.ofLE_comp_ofLE
          (filteredComplexBoundaryPlus K r p q)
          (filteredComplexCyclePlus K r p q)
          ((K.X (p + q)).filtration.obj p)
          (filteredComplex_boundary_le_cycle K r p q) hZ0)
  exact ⟨{
    B := Subobject.mk bMap
    Z := Subobject.mk zMap
    B_le_Z := hBZ
    B_component := by
      let e : (Subobject.mk bMap : C) ≅ bObj := {
        hom := (Subobject.underlyingIso bMap).hom
        inv := (Subobject.underlyingIso bMap).inv
        hom_inv_id := (Subobject.underlyingIso bMap).hom_inv_id
        inv_hom_id := (Subobject.underlyingIso bMap).inv_hom_id
      }
      exact ⟨by simpa [bObj, filteredComplexB,
        Formalization.Books.Homology.Unit20.subquotientObject] using e⟩
    Z_component := by
      let e : (Subobject.mk zMap : C) ≅ zObj := {
        hom := (Subobject.underlyingIso zMap).hom
        inv := (Subobject.underlyingIso zMap).inv
        hom_inv_id := (Subobject.underlyingIso zMap).hom_inv_id
        inv_hom_id := (Subobject.underlyingIso zMap).inv_hom_id
      }
      exact ⟨by simpa [zObj, filteredComplexZ,
        Formalization.Books.Homology.Unit20.subquotientObject] using e⟩
  }⟩

structure FilteredComplexPageDifferentials {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) where
  /-- The parameter `r` represents the source page `E_(r+1)`. -/
  differential : ∀ (r : ℕ) (p q : ℤ),
    filteredComplexPage K (r + 1 : ℕ) p q ⟶
      filteredComplexPage K (r + 1 : ℕ) (p + r + 1) (q - r)
  square_zero : ∀ (r : ℕ) (p q : ℤ),
    differential r p q ≫ differential r (p + r + 1) (q - r) = 0
  lift_rule : ∀ (r : ℕ) (p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K (r + 1 : ℕ) p q : C))
    (zNext : T ⟶
      (filteredComplexCyclePlus K (r + 1 : ℕ) (p + r + 1) (q - r) : C))
    (_hz : zNext ≫
        (filteredComplexCyclePlus K (r + 1 : ℕ) (p + r + 1) (q - r)).arrow =
      z ≫ (filteredComplexCyclePlus K (r + 1 : ℕ) p q).arrow ≫
        filteredComplexDifferential K (p + q) ≫
          eqToHom (congrArg (fun n : ℤ => (K.X n).carrier)
            (by omega))),
    filteredComplexPageClass K (r + 1 : ℕ) p q z ≫ differential r p q =
      filteredComplexPageClass K (r + 1 : ℕ) (p + r + 1) (q - r) zNext
  lift_exists : ∀ (r : ℕ) (p q : ℤ) {T : C}
    (z : T ⟶ (filteredComplexCyclePlus K (r + 1 : ℕ) p q : C))
    (_hcore : (filteredComplexCycleCore K (r + 1 : ℕ) p q).Factors
      (z ≫ (filteredComplexCyclePlus K (r + 1 : ℕ) p q).arrow)), ∃ zNext,
      (zNext ≫
          (filteredComplexCyclePlus K (r + 1 : ℕ) (p + r + 1) (q - r)).arrow =
        z ≫ (filteredComplexCyclePlus K (r + 1 : ℕ) p q).arrow ≫
          filteredComplexDifferential K (p + q) ≫
            eqToHom (congrArg (fun n : ℤ => (K.X n).carrier)
              (by omega))) ∧
        filteredComplexPageClass K (r + 1 : ℕ) p q z ≫ differential r p q =
          filteredComplexPageClass K (r + 1 : ℕ) (p + r + 1) (q - r) zNext
theorem filteredComplex_page_differentials_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexPageDifferentials K) := by
  sorry

noncomputable def filteredComplexPageDifferentials
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    FilteredComplexPageDifferentials K :=
  Classical.choice (filteredComplex_page_differentials_exists K)

abbrev filteredComplexD {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r : ℕ) (p q : ℤ) :
    filteredComplexPage K (r + 1 : ℕ) p q ⟶
      filteredComplexPage K (r + 1 : ℕ) (p + r + 1) (q - r) :=
  (filteredComplexPageDifferentials K).differential r p q

theorem filteredComplexD_squared
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (r : ℕ) (p q : ℤ) :
    filteredComplexD K r p q ≫ filteredComplexD K r (p + r + 1) (q - r) = 0 := by
  exact (filteredComplexPageDifferentials K).square_zero r p q

/-! ### The bigraded spectral sequence -/

def bigradedShift {C : Type u} [Category.{v} C] (a b : ℤ) :
    GradedObject (ℤ × ℤ) C ⥤ GradedObject (ℤ × ℤ) C :=
  GradedObject.comap C (fun x => (a + x.1, b + x.2))

structure FilteredComplexSpectralSequence {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
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
              congr 1; ring_nf) :
              (bigradedShift r (-r + 1)).obj (page r)
                  (p - r, q + r - 1) ⟶ page r (p, q)))))
        (Subobject.mk (kernel.ι (differential r (p, q))))
        (by
          let hp : (r + (p - r), (-r + 1) + (q + r - 1)) = (p, q) := by
            congr 1 <;> ring_nf
          let hs0 : (bigradedShift r (-r + 1)).obj (page r)
              (p - r, q + r - 1) = page r
                (r + (p - r), (-r + 1) + (q + r - 1)) := by
            change page r
              (r + (p - r), (-r + 1) + (q + r - 1)) = page r
                (r + (p - r), (-r + 1) + (q + r - 1))
            rfl
          let h0 : page r
              (r + (p - r), (-r + 1) + (q + r - 1)) = page r (p, q) :=
            congrArg (page r) hp
          let h : (bigradedShift r (-r + 1)).obj (page r)
              (p - r, q + r - 1) = page r (p, q) := hs0.trans h0
          let f := differential r (p - r, q + r - 1) ≫
            (eqToHom h :
              (bigradedShift r (-r + 1)).obj (page r)
                  (p - r, q + r - 1) ⟶ page r (p, q))
          let d := differential r (p, q)
          change Subobject.mk (Abelian.image.ι f) ≤ Subobject.mk (kernel.ι d)
          apply Subobject.mk_le_mk_of_comm
            (kernel.lift d (Abelian.image.ι f) (by
              apply Abelian.image_ι_comp_eq_zero
              have hsq := congrFun (square_zero r) (p - r, q + r - 1)
              change differential r (p - r, q + r - 1) ≫
                differential r (r + (p - r), (-r + 1) + (q + r - 1)) = 0 at hsq
              dsimp [f, d]
              rw [Category.assoc]
              convert hsq using 1
              · congr 1; ring_nf
              · let ht : (bigradedShift r (-r + 1)).obj (page r) (p, q) =
                    (bigradedShift r (-r + 1)).obj (page r)
                      (r + (p - r), (-r + 1) + (q + r - 1)) :=
                  congrArg
                    (fun x : ℤ × ℤ =>
                      (bigradedShift r (-r + 1)).obj (page r) x) hp.symm
                have hn := eqToHom_naturality (differential r) hp
                have hleft :
                    eqToHom h ≫ differential r (p, q) ≍
                      differential r
                        (r + (p - r), (-r + 1) + (q + r - 1)) := by
                  have hn' :
                      eqToHom h ≫ differential r (p, q) =
                        differential r
                            (r + (p - r), (-r + 1) + (q + r - 1)) ≫
                          eqToHom ht.symm := by
                    change eqToHom (hs0.trans h0) ≫ differential r (p, q) =
                      differential r
                          (r + (p - r), (-r + 1) + (q + r - 1)) ≫
                        eqToHom ht.symm
                    have hc := congrArg
                      (fun f => eqToHom hs0 ≫ f) hn.symm
                    convert hc using 1;
                      simp; rfl
                  exact (heq_of_eq hn').trans (comp_eqToHom_heq _ _)
                exact heq_comp rfl hs0 ht HEq.rfl hleft
              · simpa only [zero_comp] using
                  (comp_eqToHom_heq
                    (0 : page r (p - r, q + r - 1) ⟶
                      (bigradedShift r (-r + 1)).obj (page r)
                        (r + (p - r), (-r + 1) + (q + r - 1)))
                    (congrArg
                      (fun x : ℤ × ℤ =>
                        (bigradedShift r (-r + 1)).obj (page r) x) hp))
              ))
          simp [f, d]))
  page_differentials : FilteredComplexPageDifferentials K
  component_iso : ∀ (r : ℕ) (p q : ℤ),
    Nonempty (page r (p, q) ≅ filteredComplexPage K (r : ℤ) p q)
  differential_compatibility : ∀ (r : ℕ) (p q : ℤ), ∃
    e₀ : page (r + 1) (p, q) ≅ filteredComplexPage K (r + 1 : ℕ) p q,
    ∃ e₁ : page (r + 1) (p + r + 1, q - r) ≅
      filteredComplexPage K (r + 1 : ℕ) (p + r + 1) (q - r),
    differential (r + 1) (p, q) ≫
        eqToHom (by
          change page (r + 1)
            ((r + 1 : ℤ) + p, (-(r + 1 : ℤ) + 1) + q) =
            page (r + 1) (p + r + 1, q - r)
          congr 1; ring_nf) ≫ e₁.hom =
      e₀.hom ≫ page_differentials.differential r p q
  zero_differential_compatibility : ∀ p q : ℤ, ∃
    e₀ : page 0 (p, q) ≅ filteredComplexE₀ K p q,
    ∃ e₁ : page 0 (p, q + 1) ≅ filteredComplexE₀ K p (q + 1),
    differential 0 (p, q) ≫
        eqToHom (by
          change page 0 (0 + p, 1 + q) = page 0 (p, q + 1)
          congr 1; ring_nf) ≫ e₁.hom =
      e₀.hom ≫ filteredComplexD₀ K p q
  zero_page : ∀ p q : ℤ,
    Nonempty (page 0 (p, q) ≅ filteredComplexE₀ K p q)
  first_page : ∀ p q : ℤ,
    Nonempty (page 1 (p, q) ≅ filteredComplexE₁ K p q)

/-
Proof roadmap for `filteredComplex_spectral_sequence_exists`.

The record above is sufficiently specified: `next_page` names the actual
image/kernel subquotient, while `differential_compatibility` and
`zero_differential_compatibility` compare both kinds of chosen page
differential with their source models.  The `Nonempty`
wrappers are appropriate here because kernels, images, and cokernels are only
canonical up to isomorphism; no field needs strengthening.

Keep the construction small by first adding the following source-local helper
lemmas immediately above this theorem.

1. Construct
   `filteredComplex_zero_page_iso (K) (p q) :
      filteredComplexPage K 0 p q ≅ filteredComplexE₀ K p q`.
   Prove separately that
   `filteredComplexCyclePlus K 0 p q = (K.X (p + q)).filtration.obj p`
   and
   `filteredComplexBoundaryPlus K 0 p q =
      (K.X (p + q)).filtration.obj (p + 1)`.
   For the cycle equality, use `FilteredHom.map_filtration` for
   `K.d (p + q) (p + q + 1)`, the pullback adjunction, and
   `filteredComplexCycleCore`; for the boundary equality use the same
   filtration-preservation statement for
   `K.d (p + q - 1) (p + q)`, the exists adjunction, and
   `filteredComplexBoundaryCore`.  The exact subobject APIs are
   `CategoryTheory.Limits.pullback_factors_iff` and
   `(Subobject.existsPullbackAdj _).homEquiv`.  Finish by rewriting
   `filteredComplexPage`, `filteredComplexE₀`, and
   `Formalization.Books.Homology.Unit20.subquotientObject`.  Do not ask `simp`
   to unfold the filtered objects globally.

2. Package the page-to-page calculation as a left homology datum.  For
   `r : ℕ`, `p q : ℤ`, put `n : ℤ := p + q` and let the source page be
   `filteredComplexE₀ K p q` when `r = 0`, and
   `filteredComplexPage K (r : ℤ) p q` when `r > 0`.  Let `f` be the incoming
   differential from `(p - r, q + r - 1)` after the displayed `eqToHom`, and
   let `d` be the outgoing differential at `(p,q)`.  In the successor case
   write `r = s + 1` and use
   `(filteredComplexPageDifferentials K).differential s`; its bidegree is
   `(s+1,-s)`, i.e. `(r,-r+1)`.  Build a
   `ShortComplex.LeftHomologyData (ShortComplex.mk f d ...)` whose homology
   object is `filteredComplexPage K (r + 1 : ℕ) p q`.

   The kernel object should be the intermediate quotient
   `Z_(r+1) / B_r`.  Its map into `Z_r / B_r` is induced by
   `filteredComplex_cycle_antitone K r p q`; its projection onto
   `Z_(r+1) / B_(r+1)` is induced by
   `filteredComplex_boundary_monotone K r p q`.  Prove the kernel universal
   property using
   `FilteredComplexPageDifferentials.lift_rule` and
   `FilteredComplexPageDifferentials.lift_exists` from this file.  Prove the
   cokernel universal property by identifying the incoming image with
   `B_(r+1) / B_r`; use `Subobject.factorThru`,
   `Subobject.factorThru_arrow`, `Abelian.factorThruImage`, `cokernel.desc`,
   and `cokernel.π_desc`.  The epi-cancellation pattern in
   `differentialObjectSelfMap_page_formula` in
   `Formalization/Books/Homology/Unit22/DifferentialObjects.lean` is the
   reusable model for this quotient-of-quotients argument.  Give `f`, `d`,
   the intermediate quotient, and both structure maps explicit types so that
   Lean does not unfold all four filtration subobjects during unification.

   Split off `r = 0`: there the short complex is the three consecutive terms
   of `filteredComplexGradedPiece K p`, at the integral degrees
   `n - 1`, `n`, and `n + 1`.  Use
   `HomologicalComplex.homologyIsoSc'` and
   `ShortComplex.LeftHomologyData.homologyIso` (Mathlib,
   `Algebra/Homology/ShortComplex/HomologicalComplex.lean` and
   `.../Homology.lean`) to obtain both
   `filteredComplexPage K 1 p q ≅ filteredComplexE₁ K p q` and the page-zero
   `next_page` isomorphism.  Record, as a separate simp-free lemma, how the
   hom of this isomorphism acts on a class from
   `filteredComplexCycleCore K 1 p q`; the useful API equations are
   `HomologicalComplex.π_homologyIsoSc'_hom` and
   `ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom`.  The d1
   proof below must reuse this exact isomorphism and class formula.

3. For the quotient occurring literally in `next_page`, build the canonical
   second `ShortComplex.LeftHomologyData` with
   `K := (Subobject.mk (kernel.ι d) : C)` and
   `H := subquotientObject (Subobject.mk (Abelian.image.ι f))
      (Subobject.mk (kernel.ι d)) _`.  Transport `kernelIsKernel d` across
   `Subobject.underlyingIso (kernel.ι d)`; the cokernel part is
   `cokernelIsCokernel _`.  Compose the inverse of the explicit-page datum's
   `homologyIso` with this canonical datum's `homologyIso`.  This gives
   exactly the orientation demanded by `next_page`.  Reuse the already
   elaborated image-to-kernel proof in the field type; only the two homology
   presentations need comparison.

4. Define the record page by cases:
   `page 0 (p,q) := filteredComplexE₀ K p q` and
   `page (r+1) (p,q) := filteredComplexPage K (r+1 : ℕ) p q`.
   A `GradedObject (ℤ × ℤ) C` is a dependent function, so define the page and
   its morphisms componentwise.  At page zero use `filteredComplexD₀`; at
   page `r+1` use
   `(filteredComplexPageDifferentials K).differential r p q`, followed by the
   one `eqToHom` from `(p + r + 1, q - r)` to the raw shifted index
   `((r+1 : ℤ) + p, (-(r+1 : ℤ) + 1) + q)`.

   Prove `square_zero` componentwise with `GradedObject.hom_ext`.  The zero
   case is `(filteredComplexGradedPiece K p).d_comp_d` at `n,n+1,n+2`, after
   `filteredComplex_D₀_formula`; the successor case is
   `FilteredComplexPageDifferentials.square_zero`.  Normalize only the three
   integral index equalities with `omega`/`ring_nf`; the transports already
   present in the structure fields should not be rebuilt.

5. Fill `component_iso` by the inverse of
   `filteredComplex_zero_page_iso` at page zero and `Iso.refl _` on successor
   pages.  Fill `zero_page` by `Iso.refl _`, `first_page` with the isomorphism
   from step 2, and `next_page` with step 3.  Set `page_differentials :=
   filteredComplexPageDifferentials K`.  The successor differential was
   defined from that same value, so `differential_compatibility` reduces to
   cancellation of the two `eqToHom`s.  Witness
   `zero_differential_compatibility` by `Iso.refl _` at both ends; it reduces
   to `filteredComplexD₀` and the index equality `1 + q = q + 1`.  Finish both
   fields with `simpa only` using `Category.comp_id`, `Category.assoc`, and
   proof irrelevance.

Do not try to copy a value furnished by
`Formalization.Books.Homology.Unit20.filteredComplex_spectral_sequence_exists`:
the older record has no field relating its opaque differential to the chosen
`FilteredComplexPageDifferentials`, so it cannot discharge the enhanced
compatibility field.
-/
theorem filteredComplex_spectral_sequence_exists
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    Nonempty (FilteredComplexSpectralSequence K) := by
  sorry

noncomputable def filteredComplexSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    FilteredComplexSpectralSequence K :=
  Classical.choice (filteredComplex_spectral_sequence_exists K)

/-! ### The `d₁` exact sequence and filtration-raising case -/

abbrev filteredComplexStepComplex {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexStepComplex K p

abbrev filteredComplexD1ShortExact {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (p : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  Formalization.Books.Homology.Unit20.filteredComplexD1ShortExact K p

theorem filteredComplexD1_short_exact
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    (filteredComplexD1ShortExact K p).ShortExact := by
  exact Formalization.Books.Homology.Unit20.filteredComplexD1_boundary_description K p

noncomputable def filteredComplexD1Boundary {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    (filteredComplexD1ShortExact K p).X₃.homology (p + q) ⟶
      (filteredComplexD1ShortExact K p).X₁.homology (p + q + 1) :=
  cochainConnectingMap (filteredComplexD1_short_exact K p) (p + q)

structure FilteredComplexD1BoundaryData {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  d₁ : ∀ p q : ℤ, filteredComplexE₁ K p q ⟶ filteredComplexE₁ K (p + 1) q
  boundary : ∀ p q : ℤ,
    filteredComplexE₁ K p q ⟶ filteredComplexE₁ K (p + 1) q
  boundary_is_connecting : ∀ p q : ℤ,
    ∃ e₀ : filteredComplexE₁ K p q ≅
        (filteredComplexD1ShortExact K p).X₃.homology (p + q),
      ∃ e₁ : filteredComplexE₁ K (p + 1) q ≅
        (filteredComplexD1ShortExact K p).X₁.homology (p + q + 1),
        boundary p q = e₀.hom ≫ filteredComplexD1Boundary K p q ≫ e₁.inv
  page_differential_is_d₁ : ∀ p q : ℤ, ∃
    e₀ : filteredComplexPage K (1 : ℕ) p q ≅ filteredComplexE₁ K p q,
    ∃ e₁ : filteredComplexPage K (1 : ℕ) (p + 1) q ≅
      filteredComplexE₁ K (p + 1) q,
    filteredComplexD K 0 p q ≫
        eqToHom (by congr 1 <;> omega) ≫ e₁.hom = e₀.hom ≫ d₁ p q
  d₁_is_boundary : ∀ p q : ℤ, d₁ p q = boundary p q

/-
Proof roadmap for `filteredComplex_d1_boundary_data_exists`.

The structure is not under-specified.  Its `boundary` is required to be the
fixed Snake-Lemma map `filteredComplexD1Boundary`, and the last two fields say
that this same map is the page-one differential after the displayed
isomorphisms.  The existential isomorphisms only account for categorical
choices and the equality `(p + 1) + q = p + q + 1`.

1. Reuse the *specific* page-one isomorphism and representative formula built
   in step 2 of the preceding roadmap; an arbitrary inhabitant of a
   `Nonempty (filteredComplexPage K 1 p q ≅ filteredComplexE₁ K p q)` does not
   carry enough information to prove the comparison.

2. For each `p q`, choose the two already proved identifications
   `Formalization.Books.Homology.Unit20.filteredComplexD1_target_homology_iso
      K p q`
   and
   `Formalization.Books.Homology.Unit20.filteredComplexD1_source_homology_iso
      K p q`
   from `Formalization/Books/Homology/Unit20/FilteredComplexes.lean`.
   The first is `Iso.refl`; the second is the `eqToIso` induced by
   `(p + 1) + q = p + q + 1`.  Name them with the explicit types appearing in
   `boundary_is_connecting`.  Define
   `boundary p q := e₀.hom ≫ filteredComplexD1Boundary K p q ≫ e₁.inv`
   and set `d₁ := boundary`.  Then `boundary_is_connecting` is witnessed by
   these same `e₀,e₁`, and `d₁_is_boundary` is reflexivity.

3. Isolate the only mathematical comparison as a helper with the exact
   conclusion of `page_differential_is_d₁`.  Put `n : ℤ := p + q` and
   `S := filteredComplexD1ShortExact K p`.  Precompose the desired equality
   with the page-class map from
   `(filteredComplexCycleCore K 1 p q : C)`.  Prove this map is epi: the
   complementary summand `(K.X n).filtration.obj (p + 1)` in
   `filteredComplexCyclePlus` already lies in
   `filteredComplexBoundaryPlus K 1 p q`, so the cokernel projection is
   generated by the core summand.  Use `cokernel.π_desc`, `epi_of_epi_fac`,
   and the two `le_sup_*` inclusions, then cancel this epi at the end.

4. Apply
   `(filteredComplexPageDifferentials K).lift_exists 0 p q` to the inclusion
   of that cycle core.  It supplies the target representative `zNext`, its
   equality with the original differential in degree `n`, and exactly the
   page-class equation for `filteredComplexD K 0 p q`.  Thus the left side of
   the comparison is reduced to the page class of `zNext`; use only the
   integral normalization `(p + 0 + 1, q - 0) = (p + 1,q)` for the field's
   `eqToHom`.

5. Compute the connecting-map side with
   `CategoryTheory.ShortComplex.ShortExact.δ_eq` from Mathlib
   `Algebra/Homology/HomologySequence.lean`; do not unfold the Snake Lemma.
   Instantiate it at `i := n`, `j := n + 1`, and `k := n + 2` for
   `ComplexShape.up ℤ`.  Use these three explicitly typed representatives:
   the core representative modulo `F^(p+1)` in `S.X₃.X n`, the same
   representative modulo `F^(p+2)` in `S.X₂.X n`, and its differential modulo
   `F^(p+2)` in `S.X₁.X (n+1)`.  The two hypotheses of `δ_eq` are the component
   formulas for `filteredComplexD1Projection` and
   `filteredComplexD1Inclusion`; prove them by cancelling their defining
   cokernel epis and using `cokernel.π_desc`.  The core factorization is the
   cycle hypothesis required by `HomologicalComplex.liftCycles`.

6. Rewrite `cochainConnectingMap` only far enough to expose
   `(filteredComplexD1_short_exact K p).δ n (n+1) _`.  The result of `δ_eq`
   is the homology class of the differential representative.  Convert its
   source and target with
   `HomologicalComplex.π_homologyIsoSc'_hom`,
   `ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom`, and the
   page-one class formula from step 1.  This identifies it with the page class
   of `zNext`.  Cancel the epi from step 3, insert the target/source
   `eqToIso`s from step 2, and use the resulting equality to fill
   `page_differential_is_d₁`; the record then assembles directly.

Avoid choosing the page-one isomorphisms independently in the two fields:
without the representative formula there is no route from the opaque
categorical isomorphism to `ShortComplex.ShortExact.δ_eq`.
-/
theorem filteredComplex_d1_boundary_data_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    Nonempty (FilteredComplexD1BoundaryData K) := by
  sorry

def FilteredComplexRaisesFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ (n p : ℤ),
    (K.X n).filtration.obj p ≤
      (Subobject.pullback (filteredComplexDifferential K n)).obj
        ((K.X (n + 1)).filtration.obj (p + 1))

theorem filteredComplexRaisesFiltration_zero_graded_differential
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexRaisesFiltration K) (p q : ℤ) :
    filteredComplexD₀ K p q = 0 := by
  sorry

theorem filteredComplexRaisesFiltration_E₁_source_formula
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexRaisesFiltration K) (p q : ℤ) :
    Nonempty (filteredComplexE₁ K p q ≅ gradedPiece (K.X (p + q)) p) := by
  sorry

/-! ### Functoriality -/

/- A map of filtered complexes sends representatives of every page to
   representatives of the corresponding page.  Recording this property is
   what makes the page map below induced by the filtered-complex map rather
   than an arbitrary morphism between two chosen spectral sequences. -/
def FilteredComplexPageMapInducedBy {C : Type u} [Category.{v} C]
    [Abelian C] {K L : FilteredComplex C} (f : K ⟶ L) (r : ℕ) (p q : ℤ)
    (u : filteredComplexPage K (r : ℤ) p q ⟶
      filteredComplexPage L (r : ℤ) p q) : Prop :=
  ∀ {T : C} (z : T ⟶
      (filteredComplexCyclePlus K (r : ℤ) p q : C)), ∃ zNext,
    zNext ≫ (filteredComplexCyclePlus L (r : ℤ) p q).arrow =
      z ≫ (filteredComplexCyclePlus K (r : ℤ) p q).arrow ≫
        FilteredHom.hom (f.f (p + q)) ∧
      filteredComplexPageClass K (r : ℤ) p q z ≫ u =
        filteredComplexPageClass L (r : ℤ) p q zNext

structure FilteredComplexSpectralSequenceHom {C : Type u}
    [Category.{v} C] [Abelian C] {K L : FilteredComplex C}
    (f : K ⟶ L)
    (Sₖ : FilteredComplexSpectralSequence K)
    (Sₗ : FilteredComplexSpectralSequence L) where
  pageHom : ∀ r : ℕ, Sₖ.page r ⟶ Sₗ.page r
  compatible : ∀ r : ℕ,
    pageHom r ≫ Sₗ.differential r =
      Sₖ.differential r ≫ (bigradedShift r (-r + 1)).map (pageHom r)
  component_induced : ∀ (r : ℕ) (p q : ℤ), ∃ u,
    FilteredComplexPageMapInducedBy f r p q u ∧
      ∃ eₖ : Sₖ.page r (p, q) ≅ filteredComplexPage K (r : ℤ) p q,
      ∃ eₗ : Sₗ.page r (p, q) ≅ filteredComplexPage L (r : ℤ) p q,
        eₖ.hom ≫ u = pageHom r (p, q) ≫ eₗ.hom

theorem filteredComplex_functoriality
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) :
    ∀ (Sₖ : FilteredComplexSpectralSequence K)
      (Sₗ : FilteredComplexSpectralSequence L),
      Nonempty (FilteredComplexSpectralSequenceHom f Sₖ Sₗ) := by
  sorry

/-! ## Induced cohomology filtration -/

abbrev filteredComplexUnderlying {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : CochainComplex C ℤ :=
  Formalization.Books.Homology.Unit20.filteredComplexUnderlying K

abbrev filteredComplexCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexCohomology K n

abbrev filteredComplexStepCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexStepCohomology K n p

abbrev filteredComplexCohomologyFilteredObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    FilteredObject C :=
  Formalization.Books.Homology.Unit20.filteredComplexCohomologyFilteredObject K n

theorem filteredComplex_induced_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    (filteredComplexCohomologyFilteredObject K n).filtration.obj p =
      Formalization.Books.Homology.Unit20.filteredComplexCohomologyFiltrationStep
        K n p := rfl

def filteredComplexKernelSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) :
  Subobject (K.X n).carrier :=
  kernelSubobject ((filteredComplexUnderlying K).d n (n + 1))

def filteredComplexImageSubobject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (n : ℤ) :
  Subobject (K.X n).carrier :=
  @imageSubobject C _ _ _ ((filteredComplexUnderlying K).d (n - 1) n)
    (HasImages.has_image _)

def filteredComplexCohomologyNumerator {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    Subobject (K.X n).carrier :=
  (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p) ⊔
    filteredComplexImageSubobject K n

def filteredComplexCohomologyGradedDenominator {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) :
    Subobject (K.X n).carrier :=
  (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj (p + 1)) ⊔
    (filteredComplexImageSubobject K n ⊓ (K.X n).filtration.obj p)

noncomputable def filteredComplexCohomologyFormulaObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  subquotientObject (filteredComplexImageSubobject K n)
    (filteredComplexCohomologyNumerator K n p) le_sup_right

noncomputable def filteredComplexCohomologyGradedFormulaObject {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n p : ℤ) : C :=
  subquotientObject (filteredComplexCohomologyGradedDenominator K n p)
    (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p)
    (by
      apply sup_le
      · exact inf_le_inf_left _ ((K.X n).filtration.antitone (by omega))
      · let hImage : HasImage ((filteredComplexUnderlying K).d (n - 1) n) :=
          HasImages.has_image _
        exact inf_le_inf
          (image_le_kernel
            ((filteredComplexUnderlying K).d (n - 1) n)
            ((filteredComplexUnderlying K).d n (n + 1))
            ((filteredComplexUnderlying K).d_comp_d (n - 1) n (n + 1))) le_rfl
    )

theorem filteredComplex_cohomology_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    Nonempty (((filteredComplexCohomologyFilteredObject K n).filtration.obj p : C)
      ≅ filteredComplexCohomologyFormulaObject K n p) := by
  sorry

theorem filteredComplex_cohomology_graded_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (n p : ℤ) :
    Nonempty (gradedPiece (filteredComplexCohomologyFilteredObject K n) p ≅
      filteredComplexCohomologyGradedFormulaObject K n p) := by
  sorry

/-! ## Limits and convergence -/

abbrev FilteredComplexLimitData {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) :=
  Formalization.Books.Homology.Unit20.FilteredComplexLimitData K

abbrev filteredComplexLimitPage {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (L : FilteredComplexLimitData K)
    (p q : ℤ) : C :=
  Formalization.Books.Homology.Unit20.filteredComplexLimitPage K L p q

/-- The limiting page assembled from the componentwise stable boundaries and
cycles.  Its `(p, q)` component is `filteredComplexLimitPage K L p q`. -/
def filteredComplexLimitGradedObject {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) (L : FilteredComplexLimitData K) :
    GradedObject (ℤ × ℤ) C :=
  fun pq => filteredComplexLimitPage K L pq.1 pq.2

def filteredComplexAssociatedGradedCohomology {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) :
    GradedObject (ℤ × ℤ) C :=
  fun pq => gradedPiece
    (filteredComplexCohomologyFilteredObject K (pq.1 + pq.2)) pq.1

def FilteredComplexLimitGradedSubquotient {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    IsSubquotientOf
      (X := gradedPiece (filteredComplexCohomologyFilteredObject K (p + q)) p)
      (Y := filteredComplexLimitGradedObject K L (p, q))

theorem filteredComplex_limit_graded_subquotient {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) :
    FilteredComplexLimitGradedSubquotient K L := by
  sorry

def filteredComplexCycleLimitRepresentative {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (filteredComplexKernelSubobject K (p + q) ⊓
      (K.X (p + q)).filtration.obj p) ⊔
    (K.X (p + q)).filtration.obj (p + 1)

def filteredComplexBoundaryLimitRepresentative {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) :
    Subobject (K.X (p + q)).carrier :=
  (filteredComplexImageSubobject K (p + q) ⊓
      (K.X (p + q)).filtration.obj p) ⊔
    (K.X (p + q)).filtration.obj (p + 1)

def FilteredComplexTopBigradedInclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) : Prop :=
  ∀ r : ℕ,
    filteredComplexCycleLimitRepresentative K p q ≤
      filteredComplexCyclePlus K (r : ℤ) p q

def FilteredComplexBottomBigradedInclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (p q : ℤ) : Prop :=
  ∀ r : ℕ,
    filteredComplexBoundaryPlus K (r : ℤ) p q ≤
      filteredComplexBoundaryLimitRepresentative K p q

theorem filteredComplex_on_top_bigraded
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (p q : ℤ) : FilteredComplexTopBigradedInclusion K p q := by
  sorry

theorem filteredComplex_at_bottom_bigraded
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (p q : ℤ) : FilteredComplexBottomBigradedInclusion K p q := by
  sorry

def FilteredComplexLimitEquationsHold {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (L : FilteredComplexLimitData K) : Prop :=
  ∀ p q : ℤ,
    L.Binf p q = filteredComplexBoundaryLimitRepresentative K p q ∧
      L.Zinf p q = filteredComplexCycleLimitRepresentative K p q

def filteredComplexWeaklyConverges {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∃ L : FilteredComplexLimitData K, FilteredComplexLimitEquationsHold K L

def filteredComplexKernelImageFiltration {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) (n : ℤ) :
    DecreasingFiltration C (K.X n).carrier where
  obj p :=
    (filteredComplexKernelSubobject K n ⊓ (K.X n).filtration.obj p) ⊔
      filteredComplexImageSubobject K n
  antitone := by
    intro p q hpq
    exact sup_le_sup
      (inf_le_inf_left _ ((K.X n).filtration.antitone hpq)) le_rfl

def FilteredComplexKernelImageAbutmentCriterion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    ∃ hF : HasIntersection (filteredComplexKernelImageFiltration K n),
      ∃ hU : HasUnion (filteredComplexKernelImageFiltration K n),
        intersection hF = filteredComplexImageSubobject K n ∧
          union hU = filteredComplexKernelSubobject K n

def FilteredComplexAbutmentCriterion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    ∃ hF : HasIntersection
        (filteredComplexCohomologyFilteredObject K n).filtration,
      ∃ hU : HasUnion
          (filteredComplexCohomologyFilteredObject K n).filtration,
        intersection hF = ⊥ ∧ union hU = ⊤

theorem filteredComplex_abutment_criterion_iff_kernel_image
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    FilteredComplexAbutmentCriterion K ↔
      FilteredComplexKernelImageAbutmentCriterion K := by
  sorry

def filteredComplexAbuts {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) : Prop :=
  filteredComplexWeaklyConverges K ∧ FilteredComplexAbutmentCriterion K

abbrev FilteredComplexCohomologyComplete {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  Formalization.Books.Homology.Unit20.FilteredComplexCohomologyComplete K

def filteredComplexRegular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p, q) = 0

def filteredComplexCoregular {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
    S.differential r (p - r, q + r - 1) = 0

def filteredComplexBoundedAt {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K)
    (r₀ : ℕ) : Prop :=
  ∀ n : ℤ, Set.Finite {p : ℤ | ¬ IsZero (S.page r₀ (p, n - p))}

def filteredComplexBounded {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∃ r₀ : ℕ, filteredComplexBoundedAt S r₀

def filteredComplexBoundedBelowAt {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K)
    (r₀ : ℕ) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero (S.page r₀ (p, n - p))

def filteredComplexBoundedBelow {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∃ r₀ : ℕ, filteredComplexBoundedBelowAt S r₀

def filteredComplexBoundedAboveAt {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K)
    (r₀ : ℕ) : Prop :=
  ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, p ≤ b → IsZero (S.page r₀ (p, n - p))

def filteredComplexBoundedAbove {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) : Prop :=
  ∃ r₀ : ℕ, filteredComplexBoundedAboveAt S r₀

theorem filteredComplex_regular_iff_stable_cycles
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexRegular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexCyclePlus K (r + 1 : ℕ) p q =
          filteredComplexCyclePlus K (r + 2 : ℕ) p q := by
  sorry

theorem filteredComplex_coregular_iff_stable_boundaries
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexCoregular S ↔
      ∀ p q : ℤ, ∃ b : ℕ, ∀ r : ℕ, b ≤ r →
        filteredComplexBoundaryPlus K (r + 1 : ℕ) p q =
          filteredComplexBoundaryPlus K (r + 2 : ℕ) p q := by
  sorry

theorem filteredComplex_bounded_iff_below_and_above
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) :
    filteredComplexBounded S ↔
      filteredComplexBoundedBelow S ∧ filteredComplexBoundedAbove S := by
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

def filteredComplexConvergesAt {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C)
    (S : FilteredComplexSpectralSequence K) : Prop :=
  filteredComplexRegular S ∧ filteredComplexAbuts K ∧
    FilteredComplexCohomologyComplete K

def filteredComplexConverges {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  ∃ S : FilteredComplexSpectralSequence K,
    filteredComplexConvergesAt K S

theorem filteredComplex_limit_equations_give_associated_graded_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (L : FilteredComplexLimitData K) :
    FilteredComplexLimitEquationsHold K L →
      Nonempty (filteredComplexAssociatedGradedCohomology K ≅
        filteredComplexLimitGradedObject K L) := by
  sorry

theorem filteredComplex_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexWeaklyConverges K ↔
      ∃ L : FilteredComplexLimitData K, FilteredComplexLimitEquationsHold K L := by
  rfl

theorem filteredComplex_abutment_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexAbuts K ↔
      filteredComplexWeaklyConverges K ∧ FilteredComplexAbutmentCriterion K := by
  sorry

theorem filteredComplex_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) :
    filteredComplexConverges K ↔
      ∃ S : FilteredComplexSpectralSequence K,
        filteredComplexConvergesAt K S := by
  sorry

/-! ## Finite filtrations and the `K₀` relation -/

abbrev FilteredComplexFiniteFiltration {C : Type u} [Category.{v} C]
    [Abelian C] (K : FilteredComplex C) : Prop :=
  Formalization.Books.Homology.Unit20.FilteredComplexFiniteFiltration K

def FilteredComplexCohomologyFiniteFiltration {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    (filteredComplexCohomologyFilteredObject K n).IsFinite

theorem filteredComplex_finite_filtration_is_bounded
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K) :
    ∀ S : FilteredComplexSpectralSequence K, filteredComplexBounded S := by
  sorry

theorem filteredComplex_finite_filtration_on_cohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K) :
    FilteredComplexCohomologyFiniteFiltration K := by
  sorry

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

theorem filteredComplex_finite_filtration_weak_serre_membership
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ, P (S.page r (p, q))) :
    ∀ n : ℤ, P (filteredComplexCohomology K n) := by
  sorry

abbrev filteredComplexAlternatingSign :=
  Formalization.Books.Homology.Unit20.filteredComplexAlternatingSign

def IsWeakSerreClosureOfPage {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) : Prop :=
  P.IsWeakSerreClass ∧
    (∀ p q : ℤ, P (S.page r (p, q))) ∧
    (∀ Q : ObjectProperty C, Q.IsWeakSerreClass →
      (∀ p q : ℤ, Q (S.page r (p, q))) → ∀ X : C, P X → Q X)

structure FilteredComplexK0AlternatingSumStatement {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass] where
  finite_cohomology : Set.Finite
    {n : ℤ | ¬ IsZero (filteredComplexCohomology K n)}
  finite_page : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}
  closure : IsWeakSerreClosureOfPage S r P
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
            KZero.classOf (⟨S.page r pq, page_mem pq.1 pq.2⟩ :
              P.FullSubcategory))

theorem filteredComplex_K0_alternating_sum
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hPclosure : IsWeakSerreClosureOfPage S r P)
    (hS : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}) :
    Nonempty (FilteredComplexK0AlternatingSumStatement K S r P) := by
  sorry

/- The source's `A'` is the smallest weak Serre subcategory containing the
   nonzero page terms.  It is represented by the intersection property below,
   rather than by an arbitrary externally chosen object property. -/
def filteredComplexPageWeakSerreClosure {C : Type u}
    [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K)
    (r : ℕ) : ObjectProperty C :=
  fun X => ∀ Q : ObjectProperty C, Q.IsWeakSerreClass →
    (∀ p q : ℤ, Q (S.page r (p, q))) → Q X

theorem filteredComplex_page_weak_serre_closure_is_weak_serre
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : FilteredComplex C} (S : FilteredComplexSpectralSequence K)
    (r : ℕ) :
    (filteredComplexPageWeakSerreClosure S r).IsWeakSerreClass := by
  sorry

structure FilteredComplexK0AlternatingSumConclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (S : FilteredComplexSpectralSequence K) (r : ℕ) where
  closure_is_weak_serre :
    (filteredComplexPageWeakSerreClosure S r).IsWeakSerreClass
  closure : IsWeakSerreClosureOfPage S r
    (filteredComplexPageWeakSerreClosure S r)
  statement : @FilteredComplexK0AlternatingSumStatement C _ _ K S r
    (filteredComplexPageWeakSerreClosure S r) closure_is_weak_serre

theorem filteredComplex_K0_alternating_sum_exists_minimal
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (hK : FilteredComplexFiniteFiltration K)
    (S : FilteredComplexSpectralSequence K) (r : ℕ)
    (hS : Set.Finite {pq : ℤ × ℤ | ¬ IsZero (S.page r pq)}) :
    Nonempty (FilteredComplexK0AlternatingSumConclusion K S r) := by
  sorry

/-! ## The trivial convergence criterion -/

abbrev FilteredComplexTrivialConvergenceHypotheses {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) :=
  Formalization.Books.Homology.Unit20.FilteredComplexTrivialConvergenceHypotheses K

structure FilteredComplexTrivialConvergenceConclusion {C : Type u}
    [Category.{v} C] [Abelian C] (K : FilteredComplex C) where
  bounded : ∃ S : FilteredComplexSpectralSequence K, filteredComplexBounded S
  cohomology_filtration_finite : FilteredComplexCohomologyFiniteFiltration K
  converges : ∃ S : FilteredComplexSpectralSequence K,
    filteredComplexBounded S ∧ filteredComplexConvergesAt K S

theorem filteredComplex_trivial_convergence
    {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C)
    (hK : FilteredComplexTrivialConvergenceHypotheses K) :
    Nonempty (FilteredComplexTrivialConvergenceConclusion K) := by
  sorry

end Formalization.Books.Homology.Unit24
