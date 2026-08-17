import Formalization.Books.Derived.Unit27.ExtGroups
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# More on Algebra, Chapter 68: spectral sequences for Ext

The source's Ext groups are the integer-graded shifted Hom groups in the
derived category.  The two spectral-sequence statements are exposed through
the filtered-complex spectral-sequence interface from Homological Algebra,
Chapter 24; this records pages, convergence, and the abutment without
introducing a second spectral-sequence construction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit27
open Formalization.Books.Homology.Unit24

universe u w

namespace Formalization.Books.MoreAlgebra.Unit68

/-! ## The Ext convention and bounded-below complexes -/

/- The source's integer-graded Ext convention is exactly the earlier
   `Formalization.Books.Derived.Unit27.DerivedExt` declaration:
   `Extⁿ_R(L, K) = Hom_{D(R)}(L, K⟦n⟧)`. -/

/-- Ext between two modules, viewed as objects concentrated in degree zero. -/
abbrev moduleExt {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M N : ModuleCat.{u} R) (n : ℤ) : Type w :=
  DerivedExt (DerivedObject M) (DerivedObject N) n

/-- A module-to-`D⁺` Ext group. -/
abbrev moduleDerivedExt {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) (n : ℤ) : Type w :=
  DerivedExt (DerivedObject M)
    ((DerivedCategory.Plus.ι (C := ModuleCat.{u} R)).obj K) n

/-- The cohomology module `Hʲ(K)` of an object of `D⁺(R)`. -/
abbrev moduleDerivedCohomology {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DPlus (ModuleCat.{u} R)) (j : ℤ) : ModuleCat.{u} R :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) j).obj K

/-- Integer-indexed cochain complexes of `R`-modules. -/
abbrev ModuleCochainComplex (R : Type u) [Ring R] :=
  CochainComplex (ModuleCat.{u} R) ℤ

/-- `K : D⁺(R)` is represented by a bounded-below module complex `L`. -/
def IsRepresentedByBoundedBelowComplex {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DPlus (ModuleCat.{u} R)) (L : ModuleCochainComplex R)
    (hL : IsBoundedBelow L) : Prop :=
  Nonempty
    ((DerivedCategory.Plus.Q (C := ModuleCat.{u} R)).obj ⟨L, hL⟩ ≅ K)

/-! ## A common convergence/abutment interface -/

/-- A filtered-complex spectral sequence converges to a prescribed graded
abelian-group-valued abutment. -/
def FilteredSpectralSequenceConvergesTo
    {C : Type u} [Category.{w} C] [Abelian C]
    {K : FilteredComplex C}
    (S : FilteredComplexSpectralSequence K) (A : ℤ → C) : Prop :=
  filteredComplexRegular S ∧ filteredComplexAbuts K ∧
    FilteredComplexCohomologyComplete K ∧
      ∀ n : ℤ, Nonempty (filteredComplexCohomology K n ≅ A n)

/-- The abelian-group object attached to `Extⁿ_R(M, K)`. -/
abbrev moduleDerivedExtObject {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) (n : ℤ) :
    AddCommGrpCat.{w} :=
  AddCommGrpCat.of (moduleDerivedExt M K n)

/-! ## The two Ext spectral sequences -/

/-- Data for the spectral sequence
`E₂ⁱʲ = Extⁱ_R(M, Hʲ(K)) ⇒ Extⁱ⁺ʲ_R(M, K)`. -/
structure FirstExtSpectralSequenceData {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) where
  filteredComplex : FilteredComplex (AddCommGrpCat.{w})
  spectralSequence : FilteredComplexSpectralSequence filteredComplex
  e₂_page : ∀ i j : ℤ,
    Nonempty
      (spectralSequence.page 2 (i, j) ≅
        AddCommGrpCat.of (moduleExt M (moduleDerivedCohomology K j) i))
  convergence :
    FilteredSpectralSequenceConvergesTo spectralSequence
      (fun n => moduleDerivedExtObject M K n)

/-- Data for the spectral sequence
`E₁ⁱʲ = Extʲ_R(M, Kⁱ) ⇒ Extⁱ⁺ʲ_R(M, K)` attached to a bounded-below
complex representing `K`. -/
structure SecondExtSpectralSequenceData {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) where
  filteredComplex : FilteredComplex (AddCommGrpCat.{w})
  spectralSequence : FilteredComplexSpectralSequence filteredComplex
  e₁_page : ∀ i j : ℤ,
    Nonempty
      (spectralSequence.page 1 (i, j) ≅
        AddCommGrpCat.of (moduleExt M (L.X i) j))
  convergence :
    FilteredSpectralSequenceConvergesTo spectralSequence
      (fun n => moduleDerivedExtObject M K n)

/-- Existence of the `E₂` Ext spectral sequence for `M` and `K ∈ D⁺(R)`. -/
theorem first_ext_spectral_sequence_exists {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) :
    Nonempty (FirstExtSpectralSequenceData M K) := by
  sorry

/-- Existence of the `E₁` Ext spectral sequence for a bounded-below complex
representing `K`. -/
theorem second_ext_spectral_sequence_exists {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) :
    Nonempty (SecondExtSpectralSequenceData M K L hL hRep) := by
  sorry

/-! ## Chosen spectral sequences and their page/abutment interfaces -/

/-- A chosen data package for the first Ext spectral sequence. -/
noncomputable def firstExtSpectralSequenceData {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) :
    FirstExtSpectralSequenceData M K :=
  Classical.choice (first_ext_spectral_sequence_exists M K)

/-- The chosen filtered-complex spectral sequence for the first Ext formula. -/
noncomputable abbrev firstExtSpectralSequence {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) :
    FilteredComplexSpectralSequence
      (firstExtSpectralSequenceData M K).filteredComplex :=
  (firstExtSpectralSequenceData M K).spectralSequence

/-- The chosen first spectral sequence has the source's `E₂` page. -/
theorem first_ext_spectral_sequence_e₂_page {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) (i j : ℤ) :
    Nonempty
      ((firstExtSpectralSequence M K).page 2 (i, j) ≅
        AddCommGrpCat.of (moduleExt M (moduleDerivedCohomology K j) i)) := by
  exact (firstExtSpectralSequenceData M K).e₂_page i j

/-- The chosen first spectral sequence converges to `Ext_Rⁿ(M, K)`. -/
theorem first_ext_spectral_sequence_converges {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R)) :
    FilteredSpectralSequenceConvergesTo (firstExtSpectralSequence M K)
      (fun n => moduleDerivedExtObject M K n) := by
  exact (firstExtSpectralSequenceData M K).convergence

/-- A chosen data package for the second Ext spectral sequence. -/
noncomputable def secondExtSpectralSequenceData {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) :
    SecondExtSpectralSequenceData M K L hL hRep :=
  Classical.choice (second_ext_spectral_sequence_exists M K L hL hRep)

/-- The chosen filtered-complex spectral sequence for the second Ext formula. -/
noncomputable abbrev secondExtSpectralSequence {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) :
    FilteredComplexSpectralSequence
      (secondExtSpectralSequenceData M K L hL hRep).filteredComplex :=
  (secondExtSpectralSequenceData M K L hL hRep).spectralSequence

/-- The chosen second spectral sequence has the source's `E₁` page. -/
theorem second_ext_spectral_sequence_e₁_page {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) (i j : ℤ) :
    Nonempty
      ((secondExtSpectralSequence M K L hL hRep).page 1 (i, j) ≅
        AddCommGrpCat.of (moduleExt M (L.X i) j)) := by
  exact (secondExtSpectralSequenceData M K L hL hRep).e₁_page i j

/-- The chosen second spectral sequence converges to `Ext_Rⁿ(M, K)`. -/
theorem second_ext_spectral_sequence_converges {R : Type u} [Ring R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (M : ModuleCat.{u} R) (K : DPlus (ModuleCat.{u} R))
    (L : ModuleCochainComplex R) (hL : IsBoundedBelow L)
    (hRep : IsRepresentedByBoundedBelowComplex K L hL) :
    FilteredSpectralSequenceConvergesTo
      (secondExtSpectralSequence M K L hL hRep)
      (fun n => moduleDerivedExtObject M K n) := by
  exact (secondExtSpectralSequenceData M K L hL hRep).convergence

end Formalization.Books.MoreAlgebra.Unit68
