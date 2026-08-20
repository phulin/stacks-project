import Formalization.Books.Homology.Unit26.DoubleComplexesOfAbelianGroups

/-!
# More on Algebra, Chapter 104: Tricks with double complexes

The source works with complexes of complexes of abelian groups indexed by the
nonnegative integers.  The earlier Homology chapters provide the canonical
double-complex and product-totalization constructions.  We record the
nonnegative support condition explicitly on the corresponding double complex.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape
open Formalization.Books.Homology.Unit13
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit26

universe u

namespace Formalization.Books.MoreAlgebra.Unit104

/-! ## Complexes of complexes and product totalization -/

/-- A double complex of abelian groups supported in the nonnegative first
degree.  Its columns are the complexes `A_p^bullet` in the source. -/
structure NonnegativeDoubleComplex where
  doubleComplex : DoubleComplex AddCommGrpCat.{u}
  supported : ∀ (p q : ℤ), p < 0 → IsZero (doubleComplex.obj p q)

/-- The complex of complexes obtained from the columns of a supported double
complex. -/
def complexOfComplexes (A : NonnegativeDoubleComplex.{u}) :
    CochainComplex (AbelianGroupCochainComplex.{u}) ℤ :=
  columnsAsComplex A.doubleComplex

/-- The product total complex attached to a supported double complex. -/
def productTotalization (A : NonnegativeDoubleComplex.{u}) :
    AbelianGroupCochainComplex.{u} :=
  productTotalComplex A.doubleComplex

/-- The map between corresponding columns induced by a map of double
complexes. -/
def columnMapOfDoubleComplexMap
    {A B : DoubleComplex AddCommGrpCat.{u}}
    (f : A ⟶ B) (p : ℤ) : column A p ⟶ column B p where
  f q := f.f p q
  comm' q r hqr := by
    have hqr' : q + 1 = r := by
      simpa only [ComplexShape.up_Rel] using hqr
    subst r
    simpa [column] using (f.comm2 p q).symm

/-- The component in degree `n` of the product-total map induced by a map of
double complexes. -/
noncomputable def productTotalMapComponent
    {A B : DoubleComplex AddCommGrpCat.{u}}
    (f : A ⟶ B) (n : ℤ) :
    productTotalTerm A n ⟶ productTotalTerm B n :=
  Pi.lift (fun p =>
    Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫ f.f p (n - p))

/-- The canonical map between product total complexes. -/
noncomputable def productTotalMap
    {A B : DoubleComplex AddCommGrpCat.{u}}
    (f : A ⟶ B) :
    productTotalComplex A ⟶ productTotalComplex B where
  f n := productTotalMapComponent f n
  comm' n m hnm := by
    have hnm' : n + 1 = m := by
      simpa only [ComplexShape.up_Rel] using hnm
    subst m
    apply Pi.hom_ext
    intro p
    simp [productTotalMapComponent, productTotalComplex,
      productTotalDifferential, productTotalTerm, Category.assoc]
    have h1 :
        f.f (p - 1) (n - (p - 1)) ≫
            B.d1 (p - 1) (n - (p - 1)) ≫
            eqToHom (by
              simp [sub_eq_add_neg, add_comm, add_left_comm]) =
          A.d1 (p - 1) (n - (p - 1)) ≫
            eqToHom (by
              simp [sub_eq_add_neg, add_comm, add_left_comm]) ≫
            f.f p (n + 1 - p) := by
      let z : ∀ r : ℤ × ℤ, A.obj r.1 r.2 ⟶ B.obj r.1 r.2 :=
        fun r => f.f r.1 r.2
      have htransport :
          f.f (p - 1 + 1) (n - (p - 1)) ≫
              eqToHom (by
                simp [sub_eq_add_neg, add_comm, add_left_comm]) =
            eqToHom (by
              simp [sub_eq_add_neg, add_comm, add_left_comm]) ≫
              f.f p (n + 1 - p) := by
        simpa [z] using
          (eqToHom_naturality z
            (show (p - 1 + 1, n - (p - 1)) =
                (p, n + 1 - p) by
              ext <;> dsimp <;> ring))
      calc
        _ = A.d1 (p - 1) (n - (p - 1)) ≫
              f.f (p - 1 + 1) (n - (p - 1)) ≫
              eqToHom (by
                simp [sub_eq_add_neg, add_comm, add_left_comm]) := by
          rw [← Category.assoc, ← f.comm1 (p - 1) (n - (p - 1))]
          simp [Category.assoc]
        _ = _ := by
          simpa [Category.assoc] using
            congrArg (fun k => A.d1 (p - 1) (n - (p - 1)) ≫ k)
              htransport
    have h2 :
        f.f p (n - p) ≫ B.d2 p (n - p) ≫
            eqToHom (by
              simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]) =
          A.d2 p (n - p) ≫
            eqToHom (by
              simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]) ≫
            f.f p (n + 1 - p) := by
      let z : ∀ r : ℤ × ℤ, A.obj r.1 r.2 ⟶ B.obj r.1 r.2 :=
        fun r => f.f r.1 r.2
      have htransport :
          f.f p (n - p + 1) ≫
              eqToHom (by
                simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]) =
            eqToHom (by
              simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]) ≫
              f.f p (n + 1 - p) := by
        simpa [z] using
          (eqToHom_naturality z
            (show (p, n - p + 1) =
                (p, n + 1 - p) by
              apply Prod.ext
              · ring
              · ring))
      calc
        _ = A.d2 p (n - p) ≫
              f.f p (n - p + 1) ≫
              eqToHom (by
                simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]) := by
          rw [← Category.assoc, ← f.comm2 p (n - p)]
          simp [Category.assoc]
        _ = _ := by
          simpa [Category.assoc] using
            congrArg (fun k => A.d2 p (n - p) ≫ k) htransport
    rw [h1]
    have h2' := congrArg (fun k => p.negOnePow •
      (Pi.π (fun r : ℤ => A.obj r (n - r)) p ≫ k)) h2
    simpa [Category.assoc, Linear.units_smul_comp] using h2'

/-! ## Source statements -/

/-- If `H^{-p}(A_p^bullet)` vanishes for every nonnegative `p`, then the
degree-zero cohomology of the product total complex vanishes. -/
theorem product_totalization_cohomology_zero
    (A : NonnegativeDoubleComplex.{u})
    (hA : ∀ p : ℤ, 0 ≤ p →
      IsZero ((cochainCohomologyFunctor AddCommGrpCat (-p)).obj
        (column A.doubleComplex p))) :
    IsZero ((cochainCohomologyFunctor AddCommGrpCat 0).obj
      (productTotalization A)) := by
  sorry

/-- A degreewise quasi-isomorphism of the columns induces a
quasi-isomorphism after product totalization. -/
theorem product_totalization_map_quasiIso
    {A B : NonnegativeDoubleComplex.{u}}
    (f : A.doubleComplex ⟶ B.doubleComplex)
    (hf : ∀ p : ℤ, 0 ≤ p → QuasiIso (columnMapOfDoubleComplexMap f p)) :
    QuasiIso (productTotalMap f) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit104
