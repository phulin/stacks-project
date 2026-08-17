import Formalization.Books.Homology.Unit20.FilteredComplexes
import Formalization.Books.Homology.Unit10.SerreSubcategories
import Formalization.Books.Homology.Unit18.DoubleComplexes

/-!
# Double complexes and their two spectral sequences

The double-complex constructions from Chapter 18 are reused here.  The
horizontal and vertical cohomology complexes are written with the canonical
homology functor, and the two total-complex filtrations are presented by
explicit subobjects of the diagonal coproducts.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit10
open Formalization.Books.Homology.Unit13
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit19

universe v u

namespace Formalization.Books.Homology.Unit20

/-! ## 20.6 Double complexes and iterated cohomology -/

abbrev doubleComplexRowCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : DoubleComplex C) (q p : ℤ) : C :=
  (cochainCohomologyFunctor C p).obj (row A q)

abbrev doubleComplexColumnCohomology {C : Type u} [Category.{v} C]
    [Abelian C] (A : DoubleComplex C) (p q : ℤ) : C :=
  (cochainCohomologyFunctor C q).obj (column A p)

noncomputable def doubleComplexVerticalCohomologyMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexColumnCohomology A p q ⟶ doubleComplexColumnCohomology A (p + 1) q :=
  (cochainCohomologyFunctor C q).map (columnMap A p)

noncomputable def doubleComplexHorizontalCohomologyMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexRowCohomology A p q ⟶ doubleComplexRowCohomology A (p + 1) q :=
  (cochainCohomologyFunctor C q).map (rowMap A p)

def doubleComplexVerticalCohomologyComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (q : ℤ) : CochainComplex C ℤ where
  X p := doubleComplexColumnCohomology A p q
  d p r := if h : p + 1 = r then h ▸ doubleComplexVerticalCohomologyMap A p q else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    sorry

def doubleComplexHorizontalCohomologyComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (q : ℤ) : CochainComplex C ℤ where
  X p := doubleComplexRowCohomology A p q
  d p r := if h : p + 1 = r then h ▸ doubleComplexHorizontalCohomologyMap A p q else 0
  shape p r hpr := by
    classical
    split_ifs with h
    · exact (hpr h).elim
    · rfl
  d_comp_d' p r s hpr hrs := by
    sorry

def doubleComplexFirstE₀ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  A.obj p q

def doubleComplexFirstD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstE₀ A p q ⟶ doubleComplexFirstE₀ A p (q + 1) :=
  p.negOnePow • A.d2 p q

def doubleComplexSecondE₀ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  A.obj q p

def doubleComplexSecondD₀ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondE₀ A p q ⟶ doubleComplexSecondE₀ A p (q + 1) :=
  A.d1 q p

abbrev doubleComplexFirstE₁ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  doubleComplexColumnCohomology A p q

noncomputable def doubleComplexFirstD₁ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstE₁ A p q ⟶ doubleComplexFirstE₁ A (p + 1) q :=
  doubleComplexVerticalCohomologyMap A p q

abbrev doubleComplexSecondE₁ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  doubleComplexRowCohomology A p q

noncomputable def doubleComplexSecondD₁ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondE₁ A p q ⟶ doubleComplexSecondE₁ A (p + 1) q :=
  q.negOnePow • doubleComplexHorizontalCohomologyMap A p q

noncomputable def doubleComplexFirstE₂ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
    (doubleComplexVerticalCohomologyComplex A q)

noncomputable def doubleComplexSecondE₂ {C : Type u} [Category.{v} C] [Abelian C]
    (A : DoubleComplex C) (p q : ℤ) : C :=
  (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
    (doubleComplexHorizontalCohomologyComplex A q)

theorem doubleComplex_first_E₀_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstE₀ A p q = A.obj p q := rfl

theorem doubleComplex_first_d₀_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstD₀ A p q = p.negOnePow • A.d2 p q := rfl

theorem doubleComplex_second_E₀_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondE₀ A p q = A.obj q p := rfl

theorem doubleComplex_second_d₀_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondD₀ A p q = A.d1 q p := rfl

theorem doubleComplex_first_E₁_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstE₁ A p q = doubleComplexColumnCohomology A p q := rfl

theorem doubleComplex_second_E₁_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondE₁ A p q = doubleComplexRowCohomology A p q := rfl

theorem doubleComplex_first_E₂_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexFirstE₂ A p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
        (doubleComplexVerticalCohomologyComplex A q) := rfl

theorem doubleComplex_second_E₂_formula
    {C : Type u} [Category.{v} C] [Abelian C] (A : DoubleComplex C) (p q : ℤ) :
    doubleComplexSecondE₂ A p q =
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) p).obj
        (doubleComplexHorizontalCohomologyComplex A q) := rfl

/-! ## The two total-complex filtrations -/

def doubleComplexFirstFiltrationMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (∐ fun i : {i : ℤ // p ≤ i} => A.obj i.1 (n - i.1)) ⟶
      (totalComplex A).X n :=
  Limits.Sigma.desc (fun i =>
    Limits.Sigma.ι (fun j : ℤ => A.obj j (n - j)) i.1)

theorem doubleComplexFirstFiltrationMap_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    Mono (doubleComplexFirstFiltrationMap A n p) := by
  sorry

def doubleComplexFirstFiltrationSubobject
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) : Subobject ((totalComplex A).X n) :=
  @Subobject.mk _ _ _ _ (doubleComplexFirstFiltrationMap A n p)
    (doubleComplexFirstFiltrationMap_mono A n p)

def doubleComplexSecondFiltrationMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    (∐ fun j : {j : ℤ // p ≤ j} => A.obj (n - j.1) j.1) ⟶
      (totalComplex A).X n :=
  Limits.Sigma.desc (fun j =>
    eqToHom (by congr 1; ring) ≫
      Limits.Sigma.ι (fun i : ℤ => A.obj i (n - i)) (n - j.1))

theorem doubleComplexSecondFiltrationMap_mono
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    Mono (doubleComplexSecondFiltrationMap A n p) := by
  sorry

def doubleComplexSecondFiltrationSubobject
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) : Subobject ((totalComplex A).X n) :=
  @Subobject.mk _ _ _ _ (doubleComplexSecondFiltrationMap A n p)
    (doubleComplexSecondFiltrationMap_mono A n p)

def doubleComplexFirstFiltration
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    DecreasingFiltration C ((totalComplex A).X n) where
  obj p := doubleComplexFirstFiltrationSubobject A n p
  antitone := by
    intro p q hpq
    sorry

def doubleComplexSecondFiltration
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    DecreasingFiltration C ((totalComplex A).X n) where
  obj p := doubleComplexSecondFiltrationSubobject A n p
  antitone := by
    intro p q hpq
    sorry

def doubleComplexFirstFilteredTerm
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : FilteredObject C where
  carrier := (totalComplex A).X n
  filtration := doubleComplexFirstFiltration A n

def doubleComplexSecondFilteredTerm
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) : FilteredObject C where
  carrier := (totalComplex A).X n
  filtration := doubleComplexSecondFiltration A n

def doubleComplexFirstFilteredDifferential
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n m : ℤ) :
    doubleComplexFirstFilteredTerm A n ⟶ doubleComplexFirstFilteredTerm A m := by
  classical
  by_cases h : n + 1 = m
  · subst m
    exact ⟨(totalComplex A).d n (n + 1), by
      intro p
      sorry⟩
  · exact 0

def doubleComplexSecondFilteredDifferential
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n m : ℤ) :
    doubleComplexSecondFilteredTerm A n ⟶ doubleComplexSecondFilteredTerm A m := by
  classical
  by_cases h : n + 1 = m
  · subst m
    exact ⟨(totalComplex A).d n (n + 1), by
      intro p
      sorry⟩
  · exact 0

def doubleComplexFirstFilteredTotal
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : FilteredComplex C where
  X n := doubleComplexFirstFilteredTerm A n
  d n m := doubleComplexFirstFilteredDifferential A n m
  shape n m hnm := by
    classical
    by_cases h : n + 1 = m
    · exact (hnm h).elim
    · simp [doubleComplexFirstFilteredDifferential, h]
  d_comp_d' n m k hnm hmk := by
    sorry

def doubleComplexSecondFilteredTotal
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : FilteredComplex C where
  X n := doubleComplexSecondFilteredTerm A n
  d n m := doubleComplexSecondFilteredDifferential A n m
  shape n m hnm := by
    classical
    by_cases h : n + 1 = m
    · exact (hnm h).elim
    · simp [doubleComplexSecondFilteredDifferential, h]
  d_comp_d' n m k hnm hmk := by
    sorry

theorem doubleComplex_first_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    ((doubleComplexFirstFilteredTotal A).X n).filtration.obj p =
      doubleComplexFirstFiltrationSubobject A n p := rfl

theorem doubleComplex_second_filtration_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n p : ℤ) :
    ((doubleComplexSecondFilteredTotal A).X n).filtration.obj p =
      doubleComplexSecondFiltrationSubobject A n p := rfl

noncomputable def doubleComplexFirstSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    FilteredComplexSpectralSequence (doubleComplexFirstFilteredTotal A) :=
  Classical.choice (filteredComplex_spectral_sequence_exists
    (doubleComplexFirstFilteredTotal A))

noncomputable def doubleComplexSecondSpectralSequence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    FilteredComplexSpectralSequence (doubleComplexSecondFilteredTotal A) :=
  Classical.choice (filteredComplex_spectral_sequence_exists
    (doubleComplexSecondFilteredTotal A))

theorem doubleComplex_first_zero_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexFirstSpectralSequence A).page 0 (p, q) ≅
      doubleComplexFirstE₀ A p q) := by
  sorry

theorem doubleComplex_second_zero_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexSecondSpectralSequence A).page 0 (p, q) ≅
      doubleComplexSecondE₀ A p q) := by
  sorry

theorem doubleComplex_first_first_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexFirstSpectralSequence A).page 1 (p, q) ≅
      doubleComplexFirstE₁ A p q) := by
  sorry

theorem doubleComplex_second_first_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexSecondSpectralSequence A).page 1 (p, q) ≅
      doubleComplexSecondE₁ A p q) := by
  sorry

theorem doubleComplex_first_second_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexFirstSpectralSequence A).page 2 (p, q) ≅
      doubleComplexFirstE₂ A p q) := by
  sorry

theorem doubleComplex_second_second_page_formula
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (p q : ℤ) :
    Nonempty ((doubleComplexSecondSpectralSequence A).page 2 (p, q) ≅
      doubleComplexSecondE₂ A p q) := by
  sorry

/-! ## Convergence and the first-quadrant criterion -/

def doubleComplexFirstWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexWeaklyConverges (doubleComplexFirstFilteredTotal A)

def doubleComplexSecondWeaklyConverges
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexWeaklyConverges (doubleComplexSecondFilteredTotal A)

def doubleComplexFirstAbuts
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexAbuts (doubleComplexFirstFilteredTotal A)

def doubleComplexSecondAbuts
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexAbuts (doubleComplexSecondFilteredTotal A)

def doubleComplexFirstConverges
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexConverges (doubleComplexFirstFilteredTotal A)

def doubleComplexSecondConverges
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexConverges (doubleComplexSecondFilteredTotal A)

theorem doubleComplex_first_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    doubleComplexFirstWeaklyConverges A ↔
      filteredComplexWeaklyConverges (doubleComplexFirstFilteredTotal A) := Iff.rfl

theorem doubleComplex_second_weak_convergence_iff
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) :
    doubleComplexSecondWeaklyConverges A ↔
      filteredComplexWeaklyConverges (doubleComplexSecondFilteredTotal A) := Iff.rfl

def DoubleComplexFiniteTotalFiltrations
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  (∀ n : ℤ, FiniteFiltration
    (doubleComplexFirstFiltration A n)) ∧
  (∀ n : ℤ, FiniteFiltration
    (doubleComplexSecondFiltration A n))

def DoubleComplexFirstQuadrantConclusion
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) : Prop :=
  filteredComplexBounded (doubleComplexFirstSpectralSequence A) ∧
  filteredComplexBounded (doubleComplexSecondSpectralSequence A) ∧
  DoubleComplexFiniteTotalFiltrations A ∧
  doubleComplexFirstConverges A ∧ doubleComplexSecondConverges A

theorem doubleComplex_first_quadrant_convergence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (hA : HasFiniteDiagonalSupport A) :
    DoubleComplexFirstQuadrantConclusion A := by
  sorry

def doubleComplexWeakSerreConclusion
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (P : ObjectProperty C) : Prop :=
  (∀ n : ℤ, P (filteredComplexCohomology
    (doubleComplexFirstFilteredTotal A) n)) ∧
  (∀ n : ℤ, P (filteredComplexCohomology
    (doubleComplexSecondFilteredTotal A) n))

theorem doubleComplex_first_quadrant_weak_serre
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (hA : HasFiniteDiagonalSupport A)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : (∃ r : ℕ, ∀ p q : ℤ, P
      ((doubleComplexFirstSpectralSequence A).page r (p, q))) ∧
      ∃ r : ℕ, ∀ p q : ℤ, P
        ((doubleComplexSecondSpectralSequence A).page r (p, q))) :
    doubleComplexWeakSerreConclusion A P := by
  sorry

/-! ## Resolution by a double complex -/

structure DoubleComplexResolutionData
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : CochainComplex C ℤ) (A : DoubleComplex C) where
  alpha : K ⟶ row A 0
  finite_diagonal : HasFiniteDiagonalSupport A
  lower_zero : ∀ p q : ℤ, q < 0 → IsZero (A.obj p q)
  vertical_exact : ∀ p q : ℤ, q ≠ 0 →
    IsZero (doubleComplexColumnCohomology A p q)
  alpha_cycle : ∀ p : ℤ, alpha.f p ≫ A.d2 p 0 = 0
  alpha_kernel_iso : ∀ p : ℤ, Nonempty
    { e : K.X p ≅ kernel (A.d2 p 0) //
      e.hom ≫ kernel.ι (A.d2 p 0) = alpha.f p }

def doubleComplexResolutionKernelMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexResolutionData K A) (p : ℤ) :
    K.X p ⟶ kernel (A.d2 p 0) :=
  kernel.lift (A.d2 p 0) (D.alpha.f p) (D.alpha_cycle p)

def doubleComplexRowZeroToTotal
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    (row A 0).X n ⟶ (totalComplex A).X n :=
  (eqToHom (by simp [row]) : (row A 0).X n ⟶ A.obj n 0) ≫
    (eqToHom (by congr 1; ring) : A.obj n 0 ⟶ A.obj n (n - n)) ≫
      Limits.Sigma.ι (fun p : ℤ => A.obj p (n - p)) n

def doubleComplexColumnZeroToTotal
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (A : DoubleComplex C) (n : ℤ) :
    (column A 0).X n ⟶ (totalComplex A).X n :=
  (eqToHom (by simp [column]) : (column A 0).X n ⟶ A.obj 0 n) ≫
    (eqToHom (by congr 1; ring) : A.obj 0 n ⟶ A.obj 0 (n - 0)) ≫
      Limits.Sigma.ι (fun p : ℤ => A.obj p (n - p)) 0

structure DoubleComplexResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexResolutionData K A) where
  map : K ⟶ totalComplex A
  component_formula : ∀ n : ℤ,
    map.f n = D.alpha.f n ≫ doubleComplexRowZeroToTotal A n

noncomputable def doubleComplexResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexResolutionData K A) : DoubleComplexResolutionMap D where
  map := by
    refine
      { f := fun n => D.alpha.f n ≫
          doubleComplexRowZeroToTotal A n
        comm' := ?_ }
    intro n m hnm
    sorry
  component_formula n := rfl

theorem doubleComplex_resolution_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexResolutionData K A) :
    QuasiIso (doubleComplexResolutionMap D).map := by
  sorry

structure DoubleComplexColumnResolutionData
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (K : CochainComplex C ℤ) (A : DoubleComplex C) where
  alpha : K ⟶ column A 0
  finite_diagonal : HasFiniteDiagonalSupport A
  lower_zero : ∀ p q : ℤ, p < 0 → IsZero (A.obj p q)
  horizontal_exact : ∀ p q : ℤ, p ≠ 0 →
    IsZero (doubleComplexRowCohomology A q p)
  alpha_cycle : ∀ q : ℤ, alpha.f q ≫ A.d1 0 q = 0
  alpha_kernel_iso : ∀ q : ℤ, Nonempty
    { e : K.X q ≅ kernel (A.d1 0 q) //
      e.hom ≫ kernel.ι (A.d1 0 q) = alpha.f q }

structure DoubleComplexColumnResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexColumnResolutionData K A) where
  map : K ⟶ totalComplex A
  component_formula : ∀ n : ℤ,
    map.f n = D.alpha.f n ≫ doubleComplexColumnZeroToTotal A n

noncomputable def doubleComplexColumnResolutionMap
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexColumnResolutionData K A) : DoubleComplexColumnResolutionMap D where
  map := by
    refine
      { f := fun n => D.alpha.f n ≫
          doubleComplexColumnZeroToTotal A n
        comm' := ?_ }
    intro n m hnm
    sorry
  component_formula n := rfl

theorem doubleComplex_column_resolution_quasiIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {K : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexColumnResolutionData K A) :
    QuasiIso (doubleComplexColumnResolutionMap D).map := by
  sorry

/-! ## Homotopy equivalence and totalization -/

structure DoubleComplexHorizontalHomotopyEquivalence
    {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : DoubleComplex C) where
  forward : A ⟶ B
  inverse : B ⟶ A
  left : HorizontalHomotopy (forward ≫ inverse) (𝟙 A)
  right : HorizontalHomotopy (inverse ≫ forward) (𝟙 B)

structure CochainHomotopyEquivalence
    {C : Type u} [Category.{v} C] [Preadditive C]
    (K L : CochainComplex C ℤ) (f : K ⟶ L) where
  inverse : L ⟶ K
  left : Nonempty (Homotopy (f ≫ inverse) (𝟙 K))
  right : Nonempty (Homotopy (inverse ≫ f) (𝟙 L))

structure DoubleComplexHomotopyComplexData
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    (M : CochainComplex C ℤ) (A : DoubleComplex C) where
  source : DoubleComplex C
  source_concentrated : ∀ p q : ℤ, p ≠ 0 → IsZero (source.obj p q)
  source_total_iso : totalComplex source ≅ M
  equivalence : DoubleComplexHorizontalHomotopyEquivalence source A
  induced : M ⟶ totalComplex A
  induced_formula : source_total_iso.hom ≫ induced =
    totalMap equivalence.forward

theorem doubleComplex_homotopy_total_equivalence
    {C : Type u} [Category.{v} C] [Abelian C] [HasCountableCoproducts C]
    {M : CochainComplex C ℤ} {A : DoubleComplex C}
    (D : DoubleComplexHomotopyComplexData M A) :
    Nonempty (CochainHomotopyEquivalence M (totalComplex A) D.induced) := by
  sorry

end Formalization.Books.Homology.Unit20
