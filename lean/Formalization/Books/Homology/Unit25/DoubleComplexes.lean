import Formalization.Books.Homology.Unit18.DoubleComplexes
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Formalization.Books.Homology.Unit13.Complexes
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Homological Algebra, Chapter 25: Spectral sequences: double complexes

This file gives a source-facing interface for the two spectral sequences
attached to the filtrations of a totalized double complex.  The double
complex, row/column, total-complex, filtered-complex, and spectral-sequence
constructions are the canonical interfaces from Chapters 18, 20, and 24.
The page formula records below make the two index conventions and the signs
in the source explicit.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit24

open scoped BigOperators

universe v u

namespace Formalization.Books.Homology.Unit25

/-! ## Iterated cohomology of a double complex -/

/-- The complex in the first index obtained by taking vertical cohomology
in a fixed second degree.  Its differential is induced by `d₁`. -/
def doubleComplexVerticalHomologyComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (q : ℤ) : CochainComplex C ℤ where
  X p :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
      (column A p)
  d p r := if h : p + 1 = r then
      h ▸ HomologicalComplex.homologyMap (columnMap A p) q
    else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    sorry

/-- The complex in the second index obtained by taking horizontal cohomology
in a fixed first degree.  Its differential is induced by `d₂`. -/
def doubleComplexHorizontalHomologyComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (q : ℤ) : CochainComplex C ℤ where
  X p :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
      (row A p)
  d p r := if h : p + 1 = r then
      h ▸ HomologicalComplex.homologyMap (rowMap A p) q
    else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    sorry

/-- The vertical cohomology object `H^q(K^{p,bullet})`. -/
abbrev doubleComplexVerticalCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (doubleComplexVerticalHomologyComplex A q).X p

/-- The horizontal cohomology object `H^q(K^{bullet,p})`. -/
abbrev doubleComplexHorizontalCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (doubleComplexHorizontalHomologyComplex A q).X p

/-- The first iterated cohomology object
`H_I^p(H_{II}^q(K))`. -/
abbrev doubleComplexFirstIteratedCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
    (doubleComplexVerticalHomologyComplex A q)

/-- The second iterated cohomology object
`H_{II}^p(H_I^q(K))`. -/
abbrev doubleComplexSecondIteratedCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
    (doubleComplexHorizontalHomologyComplex A q)

theorem doubleComplex_vertical_cohomology_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexVerticalCohomology A p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
        (column A p) := rfl

theorem doubleComplex_horizontal_cohomology_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexHorizontalCohomology A p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).obj
        (row A p) := rfl

/-! ## The two total-complex filtrations -/

/- The summands in the first filtration are indexed by the subtype
`{i // p ≤ i}`; the image of their coproduct in the diagonal coproduct is
the categorical version of `⊕_{i+j=n, i≥p} A^{i,j}`. -/
noncomputable def doubleComplexFirstFiltrationInjection
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (∐ fun i : {i : ℤ // p ≤ i} => A.obj i.1 (n - i.1)) ⟶
      (totalComplex A).X n := by
  change
    (∐ fun i : {i : ℤ // p ≤ i} => A.obj i.1 (n - i.1)) ⟶
      ∐ fun i : ℤ => A.obj i (n - i)
  exact Sigma.desc (fun i => Sigma.ι (fun j : ℤ => A.obj j (n - j)) i.1)

noncomputable def doubleComplexSecondFiltrationInjection
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (∐ fun i : {i : ℤ // p ≤ n - i} => A.obj i.1 (n - i.1)) ⟶
      (totalComplex A).X n := by
  change
    (∐ fun i : {i : ℤ // p ≤ n - i} => A.obj i.1 (n - i.1)) ⟶
      ∐ fun i : ℤ => A.obj i (n - i)
  exact Sigma.desc (fun i => Sigma.ι (fun j : ℤ => A.obj j (n - j)) i.1)

/-- The first filtration step on the degree-`n` total term. -/
noncomputable def doubleComplexFirstFiltrationStep
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    Subobject ((totalComplex A).X n) :=
  Subobject.mk (Abelian.image.ι (doubleComplexFirstFiltrationInjection A n p))

/-- The second filtration step on the degree-`n` total term. -/
noncomputable def doubleComplexSecondFiltrationStep
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    Subobject ((totalComplex A).X n) :=
  Subobject.mk (Abelian.image.ι (doubleComplexSecondFiltrationInjection A n p))

noncomputable def doubleComplexFirstFilteredTotalObject
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : FilteredObject C where
  carrier := (totalComplex A).X n
  filtration :=
    { obj := doubleComplexFirstFiltrationStep A n
      antitone := by
        intro p q hpq
        sorry }

noncomputable def doubleComplexSecondFilteredTotalObject
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : FilteredObject C where
  carrier := (totalComplex A).X n
  filtration :=
    { obj := doubleComplexSecondFiltrationStep A n
      antitone := by
        intro p q hpq
        sorry }

noncomputable def doubleComplexFirstFilteredTotalDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n m : ℤ) :
    doubleComplexFirstFilteredTotalObject A n ⟶
      doubleComplexFirstFilteredTotalObject A m :=
  ⟨(totalComplex A).d n m, by
    intro p
    sorry⟩

noncomputable def doubleComplexSecondFilteredTotalDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n m : ℤ) :
    doubleComplexSecondFilteredTotalObject A n ⟶
      doubleComplexSecondFilteredTotalObject A m :=
  ⟨(totalComplex A).d n m, by
    intro p
    sorry⟩

/-- The total complex with the filtration `F_I`. -/
noncomputable def doubleComplexFirstFilteredTotal
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) : Formalization.Books.Homology.Unit24.FilteredComplex C where
  X := doubleComplexFirstFilteredTotalObject A
  d n m := if h : n + 1 = m then
      h ▸ doubleComplexFirstFilteredTotalDifferential A n (n + 1)
    else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm h).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    sorry

/-- The total complex with the filtration `F_{II}`. -/
noncomputable def doubleComplexSecondFilteredTotal
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) : Formalization.Books.Homology.Unit24.FilteredComplex C where
  X := doubleComplexSecondFilteredTotalObject A
  d n m := if h : n + 1 = m then
      h ▸ doubleComplexSecondFilteredTotalDifferential A n (n + 1)
    else 0
  shape n m hnm := by
    classical
    split_ifs with h
    · exact (hnm h).elim
    · rfl
  d_comp_d' n m k hnm hmk := by
    sorry

theorem doubleComplex_first_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (doubleComplexFirstFilteredTotalObject A n).filtration.obj p =
      doubleComplexFirstFiltrationStep A n p := rfl

theorem doubleComplex_second_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (doubleComplexSecondFilteredTotalObject A n).filtration.obj p =
      doubleComplexSecondFiltrationStep A n p := rfl

abbrev doubleComplexFirstTotalCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : C :=
  filteredComplexCohomology (doubleComplexFirstFilteredTotal A) n

abbrev doubleComplexSecondTotalCohomology
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : C :=
  filteredComplexCohomology (doubleComplexSecondFilteredTotal A) n

/-! ## The two spectral sequences and their page formulas -/

noncomputable def doubleComplexFirstSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence
      (doubleComplexFirstFilteredTotal A) :=
  Formalization.Books.Homology.Unit24.filteredComplexSpectralSequence _

noncomputable def doubleComplexSecondSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence
      (doubleComplexSecondFilteredTotal A) :=
  Formalization.Books.Homology.Unit24.filteredComplexSpectralSequence _

/-- The page differential with its source-facing target bidegree. -/
noncomputable def doubleComplexPageDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : Formalization.Books.Homology.Unit24.FilteredComplex C}
    (S : Formalization.Books.Homology.Unit24.FilteredComplexSpectralSequence K)
    (r : ℕ) (p q : ℤ) :
    S.page r (p, q) ⟶ S.page r (p + r, q - r + 1) :=
  S.differential r (p, q) ≫
    eqToHom (by
      change S.page r (r + p, (-r + 1) + q) =
        S.page r (p + r, q - r + 1)
      congr 1; ring_nf)

abbrev doubleComplexFirstPage
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (r : ℕ) (p q : ℤ) : C :=
  (doubleComplexFirstSpectralSequence A).page r (p, q)

abbrev doubleComplexSecondPage
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (r : ℕ) (p q : ℤ) : C :=
  (doubleComplexSecondSpectralSequence A).page r (p, q)

abbrev doubleComplexFirstPageDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (r : ℕ) (p q : ℤ) :
    doubleComplexFirstPage A r p q ⟶
      doubleComplexFirstPage A r (p + r) (q - r + 1) :=
  doubleComplexPageDifferential (doubleComplexFirstSpectralSequence A) r p q

abbrev doubleComplexSecondPageDifferential
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C]
    (A : DoubleComplex C) (r : ℕ) (p q : ℤ) :
    doubleComplexSecondPage A r p q ⟶
      doubleComplexSecondPage A r (p + r) (q - r + 1) :=
  doubleComplexPageDifferential (doubleComplexSecondSpectralSequence A) r p q

structure DoubleComplexFirstSpectralSequenceTerms
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (S : FilteredComplexSpectralSequence (doubleComplexFirstFilteredTotal A))
    : Prop where
  zero_page : ∀ p q : ℤ, Nonempty (S.page 0 (p, q) ≅ A.obj p q)
  zero_differential : ∀ p q : ℤ,
    ∃ e₀ : S.page 0 (p, q) ≅ A.obj p q,
      ∃ e₁ : S.page 0 (p, q + 1) ≅ A.obj p (q + 1),
        e₀.inv ≫ doubleComplexPageDifferential S 0 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          p.negOnePow • A.d2 p q
  first_page : ∀ p q : ℤ,
    Nonempty (S.page 1 (p, q) ≅ doubleComplexVerticalCohomology A p q)
  first_differential : ∀ p q : ℤ,
    ∃ e₀ : S.page 1 (p, q) ≅ doubleComplexVerticalCohomology A p q,
      ∃ e₁ : S.page 1 (p + 1, q) ≅
        doubleComplexVerticalCohomology A (p + 1) q,
        e₀.inv ≫ doubleComplexPageDifferential S 1 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          HomologicalComplex.homologyMap (columnMap A p) q
  second_page : ∀ p q : ℤ,
    Nonempty (S.page 2 (p, q) ≅ doubleComplexFirstIteratedCohomology A p q)

structure DoubleComplexSecondSpectralSequenceTerms
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (S : FilteredComplexSpectralSequence (doubleComplexSecondFilteredTotal A))
    : Prop where
  zero_page : ∀ p q : ℤ, Nonempty (S.page 0 (p, q) ≅ A.obj q p)
  zero_differential : ∀ p q : ℤ,
    ∃ e₀ : S.page 0 (p, q) ≅ A.obj q p,
      ∃ e₁ : S.page 0 (p, q + 1) ≅ A.obj (q + 1) p,
        e₀.inv ≫ doubleComplexPageDifferential S 0 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          A.d1 q p
  first_page : ∀ p q : ℤ,
    Nonempty (S.page 1 (p, q) ≅ doubleComplexHorizontalCohomology A p q)
  first_differential : ∀ p q : ℤ,
    ∃ e₀ : S.page 1 (p, q) ≅ doubleComplexHorizontalCohomology A p q,
      ∃ e₁ : S.page 1 (p + 1, q) ≅
        doubleComplexHorizontalCohomology A (p + 1) q,
        e₀.inv ≫ doubleComplexPageDifferential S 1 p q ≫
            eqToHom (by congr 1; ring_nf) ≫ e₁.hom =
          q.negOnePow • HomologicalComplex.homologyMap (rowMap A p) q
  second_page : ∀ p q : ℤ,
    Nonempty (S.page 2 (p, q) ≅ doubleComplexSecondIteratedCohomology A p q)

/-- This is the source lemma describing all six displayed page terms and
the two signed page differentials. -/
theorem doubleComplex_spectral_sequence_terms
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) :
    DoubleComplexFirstSpectralSequenceTerms A
        (doubleComplexFirstSpectralSequence A) ∧
      DoubleComplexSecondSpectralSequenceTerms A
        (doubleComplexSecondSpectralSequence A) := by
  sorry

/-! ## Convergence -/

abbrev doubleComplexFirstWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexWeaklyConverges (doubleComplexFirstFilteredTotal A)

abbrev doubleComplexSecondWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexWeaklyConverges (doubleComplexSecondFilteredTotal A)

abbrev doubleComplexFirstAbuts
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexAbuts (doubleComplexFirstFilteredTotal A)

abbrev doubleComplexSecondAbuts
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexAbuts (doubleComplexSecondFilteredTotal A)

abbrev doubleComplexFirstConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexConverges (doubleComplexFirstFilteredTotal A)

abbrev doubleComplexSecondConverges
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  filteredComplexConverges (doubleComplexSecondFilteredTotal A)

def doubleComplexFirstWeakConvergenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (L : FilteredComplexLimitData (doubleComplexFirstFilteredTotal A)) : Prop :=
  Nonempty
    (filteredComplexAssociatedGradedCohomology
        (doubleComplexFirstFilteredTotal A) ≅
      fun pq => filteredComplexLimitPage
        (doubleComplexFirstFilteredTotal A) L pq.1 pq.2)

def doubleComplexSecondWeakConvergenceData
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (L : FilteredComplexLimitData (doubleComplexSecondFilteredTotal A)) : Prop :=
  Nonempty
    (filteredComplexAssociatedGradedCohomology
        (doubleComplexSecondFilteredTotal A) ≅
      fun pq => filteredComplexLimitPage
        (doubleComplexSecondFilteredTotal A) L pq.1 pq.2)

theorem doubleComplex_first_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) :
    doubleComplexFirstWeaklyConverges A ↔
      ∃ L, doubleComplexFirstWeakConvergenceData A L := by
  rfl

theorem doubleComplex_second_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) :
    doubleComplexSecondWeaklyConverges A ↔
      ∃ L, doubleComplexSecondWeakConvergenceData A L := by
  rfl

/-! ## Finite diagonals and the first-quadrant consequence -/

def doubleComplexFirstFilteredTotalFinite
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  FilteredComplexFiniteFiltration (doubleComplexFirstFilteredTotal A)

def doubleComplexSecondFilteredTotalFinite
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C) : Prop :=
  FilteredComplexFiniteFiltration (doubleComplexSecondFilteredTotal A)

theorem doubleComplex_finite_diagonal_support_first_filtered_total
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (hA : HasFiniteDiagonalSupport A) :
    doubleComplexFirstFilteredTotalFinite A := by
  sorry

theorem doubleComplex_finite_diagonal_support_second_filtered_total
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (hA : HasFiniteDiagonalSupport A) :
    doubleComplexSecondFilteredTotalFinite A := by
  sorry

theorem doubleComplex_first_quadrant_convergence
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (hA : HasFiniteDiagonalSupport A) :
    filteredComplexBounded (doubleComplexFirstSpectralSequence A) ∧
      filteredComplexBounded (doubleComplexSecondSpectralSequence A) ∧
      FilteredComplexCohomologyFiniteFiltration
        (doubleComplexFirstFilteredTotal A) ∧
      FilteredComplexCohomologyFiniteFiltration
        (doubleComplexSecondFilteredTotal A) ∧
      doubleComplexFirstConverges A ∧ doubleComplexSecondConverges A := by
  sorry

theorem doubleComplex_first_quadrant_weak_serre_first
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (hA : HasFiniteDiagonalSupport A) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ,
      P ((doubleComplexFirstSpectralSequence A).page r (p, q))) :
    ∀ n : ℤ, P (doubleComplexFirstTotalCohomology A n) := by
  sorry

theorem doubleComplex_first_quadrant_weak_serre_second
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (A : DoubleComplex C)
    (hA : HasFiniteDiagonalSupport A) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ,
      P ((doubleComplexSecondSpectralSequence A).page r (p, q))) :
    ∀ n : ℤ, P (doubleComplexSecondTotalCohomology A n) := by
  sorry

/-! ## The two resolution orientations -/

structure DoubleComplexResolutionHypotheses
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (A : DoubleComplex C) where
  finite_diagonal : HasFiniteDiagonalSupport A
  augmentation : K ⟶ row A 0
  supported : ∀ p q : ℤ, q < 0 → IsZero (A.obj p q)
  exact_off_zero : ∀ p q : ℤ, q ≠ 0 → IsZero ((column A p).homology q)
  augmentation_kernel_iso : ∀ p : ℤ,
    ∃ e : K.X p ≅ kernel (A.d2 p 0),
      e.hom ≫ kernel.ι (A.d2 p 0) = augmentation.f p

noncomputable def doubleComplexResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (h : DoubleComplexResolutionHypotheses K A) :
    K ⟶ T.complex where
  f n := h.augmentation.f n ≫
    eqToHom (congrArg (fun q : ℤ => A.obj n q) (by ring)) ≫
    (T.diagonal n).cocone.ι.app (Discrete.mk n) ≫ (T.term_iso n).inv
  comm' n m hnm := by
    sorry

theorem doubleComplex_resolution_totalization_exists
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (h : DoubleComplexResolutionHypotheses K A) :
    Nonempty (TotalComplexPresentation A) := by
  exact @totalComplexPresentation_exists_of_finite_support C _ _
    CategoryTheory.Abelian.hasFiniteBiproducts A h.finite_diagonal

theorem doubleComplex_gives_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (h : DoubleComplexResolutionHypotheses K A) :
    QuasiIso (doubleComplexResolutionMap T h) := by
  sorry

structure DoubleComplexSecondResolutionHypotheses
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (A : DoubleComplex C) where
  finite_diagonal : HasFiniteDiagonalSupport A
  augmentation : K ⟶ column A 0
  supported : ∀ p q : ℤ, p < 0 → IsZero (A.obj p q)
  exact_off_zero : ∀ p q : ℤ, p ≠ 0 → IsZero ((row A q).homology p)
  augmentation_kernel_iso : ∀ q : ℤ,
    ∃ e : K.X q ≅ kernel (A.d1 0 q),
      e.hom ≫ kernel.ι (A.d1 0 q) = augmentation.f q

noncomputable def doubleComplexSecondResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (h : DoubleComplexSecondResolutionHypotheses K A) :
    K ⟶ T.complex where
  f n := h.augmentation.f n ≫
    eqToHom (congrArg (fun q : ℤ => A.obj 0 q) (by ring)) ≫
    (T.diagonal n).cocone.ι.app (Discrete.mk 0) ≫ (T.term_iso n).inv
  comm' n m hnm := by
    sorry

theorem doubleComplex_gives_second_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (h : DoubleComplexSecondResolutionHypotheses K A) :
    QuasiIso (doubleComplexSecondResolutionMap T h) := by
  sorry

/-! ## Homotopy equivalences of complexes of complexes -/

abbrev doubleComplexDegreeZeroComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (M : CochainComplex C ℤ) : CochainComplex (CochainComplex C ℤ) ℤ :=
  Formalization.Books.Homology.Unit14.CochainComplex.concentrated
    (CochainComplex C ℤ) M 0

abbrev doubleComplexComplexOfComplexes
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) : CochainComplex (CochainComplex C ℤ) ℤ :=
  columnsAsComplex A

noncomputable def doubleComplexHomotopyComponent
    {C : Type u} [Category.{v} C] [Abelian C]
    {M : CochainComplex C ℤ} (A : DoubleComplex C)
    (a : doubleComplexDegreeZeroComplex M ⟶
      doubleComplexComplexOfComplexes A) (n : ℤ) :
    M.X n ⟶ A.obj 0 n :=
  eqToHom (congrArg (fun X : CochainComplex C ℤ => X.X n)
      (Formalization.Books.Homology.Unit14.CochainComplex.concentrated_at
        M 0).symm) ≫ (a.f 0).f n

noncomputable def doubleComplexHomotopyInducedMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {M : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (a : doubleComplexDegreeZeroComplex M ⟶
      doubleComplexComplexOfComplexes A) :
    M ⟶ T.complex where
  f n := doubleComplexHomotopyComponent A a n ≫
    eqToHom (congrArg (fun q : ℤ => A.obj 0 q) (by ring)) ≫
    (T.diagonal n).cocone.ι.app (Discrete.mk 0) ≫ (T.term_iso n).inv
  comm' n m hnm := by
    sorry

theorem doubleComplex_homotopy_complexes
    {C : Type u} [Category.{v} C] [Abelian C]
    {M : CochainComplex C ℤ} {A : DoubleComplex C}
    (T : TotalComplexPresentation A)
    (a : doubleComplexDegreeZeroComplex M ⟶
      doubleComplexComplexOfComplexes A)
    (ha : Formalization.Books.Homology.Unit13.cochainHomotopyEquivalence a) :
    Formalization.Books.Homology.Unit13.cochainHomotopyEquivalence
      (doubleComplexHomotopyInducedMap T a) := by
  sorry

end Formalization.Books.Homology.Unit25
