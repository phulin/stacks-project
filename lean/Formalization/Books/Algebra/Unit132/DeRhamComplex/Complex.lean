import Formalization.Books.Algebra.Unit132.DeRhamComplex.Core

namespace Formalization.Books.Algebra.Unit132

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit13
open Formalization.Books.Algebra.Unit131
open scoped TensorProduct

noncomputable section
/-! ## The de Rham complex -/

/-- Cochain complexes of `A`-modules indexed by `ℕ`. -/
abbrev DeRhamComplex (A : Type*) [CommRing A] :=
  HomologicalComplex (ModuleCat A) (ComplexShape.up ℕ)

/-- The de Rham complex of `B` over `A`. -/
noncomputable def deRhamComplex
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
    DeRhamComplex A where
  X p := ModuleCat.of A (deRhamTerm A B p)
  d i j := if h : i + 1 = j then
    h ▸ ModuleCat.ofHom (deRhamDifferential (A := A) (B := B) i)
  else 0
  shape i j hij := by
    classical
    split_ifs with h
    · exact (hij h).elim
    · rfl
  d_comp_d' i j k hij hjk := by
    classical
    have hij' : i + 1 = j := by
      simpa only [ComplexShape.up_Rel] using hij
    have hjk' : j + 1 = k := by
      simpa only [ComplexShape.up_Rel] using hjk
    subst j
    subst k
    simp
    apply ModuleCat.hom_ext
    change (deRhamDifferential (A := A) (B := B) (i + 1)).comp
        (deRhamDifferential (A := A) (B := B) i) = 0
    exact deRhamDifferential_comp (A := A) (B := B) i

theorem deRhamComplex_differential_comp_zero
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : ℕ) :
    (deRhamComplex A B).d p (p + 1) ≫ (deRhamComplex A B).d (p + 1) (p + 2) = 0 := by
  exact (deRhamComplex A B).d_comp_d p (p + 1) (p + 2)

/-! ## Absolute de Rham complexes -/

/-- The absolute module of differentials of a ring. -/
abbrev absoluteModuleOfDifferentials (R : Type*) [CommRing R] :=
  ModuleOfDifferentials ℤ R

/-- The absolute de Rham complex of a ring. -/
noncomputable def absoluteDeRhamComplex
    (R : Type*) [CommRing R] : DeRhamComplex ℤ :=
  deRhamComplex ℤ R

theorem absolute_universal_differential_one
    {R : Type*} [CommRing R] :
    universalDifferentialLinearMap ℤ R 1 = 0 := by
  exact (universalDifferential ℤ R).map_one_eq_zero

end
end Formalization.Books.Algebra.Unit132
