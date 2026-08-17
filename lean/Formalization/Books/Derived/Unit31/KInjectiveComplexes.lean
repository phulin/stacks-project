import Formalization.Books.Derived.Unit10.DistinguishedTriangles
import Formalization.Books.Derived.Unit14.DerivedFunctors
import Formalization.Books.Derived.Unit18.InjectiveResolutions
import Formalization.Books.Homology.Unit31.InverseSystems
import Formalization.Books.Categories.Unit23.ExactFunctors
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Derived Categories, Chapter 31: K-injective complexes

The canonical K-injective predicate is Mathlib's
`CochainComplex.IsKInjective`.  This file records the source's
characterizations, closure properties, product and inverse-limit results, and
the right-derived-functor interfaces built from K-injective complexes.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit10
open Formalization.Books.Derived.Unit11
open Formalization.Books.Derived.Unit14
open Formalization.Books.Derived.Unit18
open Formalization.Books.Homology.Unit31
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u v' u'

namespace Formalization.Books.Derived.Unit31

/-! ## The definition and the Hom comparison -/

/- Mathlib's `CochainComplex.IsKInjective` is the canonical definition: maps
   from acyclic complexes are homotopic to zero.  The following theorem gives
   the source's equivalent homotopy-category formulation. -/
theorem isKInjective_iff_homotopy_hom_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) :
    I.IsKInjective ↔
      ∀ (M : BookComplex A), M.Acyclic →
        ∀ f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
          (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
          f = 0 := by
  sorry

/- The source's shift observation is recorded for every integer shift. -/
theorem isKInjective_homotopy_hom_zero_of_shift
    {A : Type u} [Category.{v} A] [Abelian A]
    {I M : BookComplex A} (hI : I.IsKInjective) (hM : M.Acyclic) (n : ℤ) :
    ∀ f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (M⟦n⟧) ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I,
      f = 0 := by
  sorry

/- The three criteria in the source are recorded as adjacent equivalences.
   Criterion (2) uses precomposition by a quasi-isomorphism, and criterion
   (3) uses the canonical localization functor `DerivedCategory.Qh`. -/
theorem isKInjective_iff_quasiIso_precomposition_bijective_iff_derived_hom_bijective
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (I : BookComplex A) :
    (I.IsKInjective ↔
        ∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f)) ∧
      ((∀ {M N : BookComplex A} (s : M ⟶ N), QuasiIso s →
          Function.Bijective
            (fun (f :
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                  (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =>
              (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map s ≫ f)) ↔
        ∀ (N : BookComplex A),
          Function.Bijective
            ((DerivedCategory.Qh (C := A)).map :
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N ⟶
                (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) →
                ((DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N) ⟶
                  (DerivedCategory.Qh (C := A)).obj
                    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) := by
  sorry

/-! ## Distinguished triangles and bounded-below complexes -/

/- The source quantifies over the three objects in a distinguished triangle.
   Here the objects are represented by explicit complexes, so the three
   possible choices of the two K-injective objects are visible in the result. -/
theorem isKInjective_two_out_of_three_of_distinguished_triangle
    {A : Type u} [Category.{v} A] [Abelian A]
    {K L M : BookComplex A}
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L)
    (g : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)
    (h : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M ⟶
      (shiftFunctor (BookHomotopyCategory A) (1 : ℤ)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))
    (hT : Triangle.mk f g h ∈ distTriang (BookHomotopyCategory A)) :
    ((K.IsKInjective ∧ L.IsKInjective) → M.IsKInjective) ∧
      ((L.IsKInjective ∧ M.IsKInjective) → K.IsKInjective) ∧
        ((M.IsKInjective ∧ K.IsKInjective) → L.IsKInjective) := by
  sorry

/- Mathlib's bounded-below injective-complex theorem is reused directly. -/
theorem isKInjective_of_bounded_below_injective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : BookComplex A) (hI : IsBoundedBelow I)
    (hIinj : ∀ n : ℤ, Injective (I.X n)) :
    I.IsKInjective :=
  isKInjective_of_bounded_below_termwise_injective I hI hIinj

/-! ## Products of K-injective complexes -/

/- The termwise products in the source are represented by the canonical
   product of complexes; evaluation of this product is the corresponding
   product of terms. -/
noncomputable def productComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) : BookComplex A :=
  ∏ᶜ I

noncomputable def productComplexProjection
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) (t : T) : productComplex I ⟶ I t :=
  Pi.π I t

theorem productComplex_eval_isProduct
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    (I : T → BookComplex A) (n : ℤ) :
    Nonempty
      (IsLimit
        (Fan.mk ((productComplex I).X n)
          (fun t => (productComplexProjection I t).f n))) := by
  sorry

/- The displayed complexes `C`, `C_t`, and the identity `C = ∏ C_t` in the
   source proof are the Hom-complex calculation underlying the following
   stronger interface; they are not separate objects needed by users. -/
noncomputable def productDerivedCone
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    [HasDerivedCategory.{w} A] (I : T → BookComplex A) :
    Fan (fun t : T =>
      (DerivedCategory.Qh (C := A)).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I t))) :=
  Fan.mk
    ((DerivedCategory.Qh (C := A)).obj
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (productComplex I)))
    (fun t =>
      (DerivedCategory.Qh (C := A)).map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          (productComplexProjection I t)))

theorem productComplex_isKInjective_and_represents_derived_product
    {A : Type u} [Category.{v} A] [Abelian A]
    {T : Type w} [HasProductsOfShape T A]
    [HasDerivedCategory.{w} A] (I : T → BookComplex A)
    (hI : ∀ t : T, (I t).IsKInjective) :
    (productComplex I).IsKInjective ∧
      Nonempty (IsLimit (productDerivedCone I)) := by
  sorry

/-! ## Derived functors computed on K-injectives -/

section DerivedFunctor

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A]
  {D' : Type u'} [Category.{v'} D'] [Preadditive D']
  [HasZeroObject D'] [HasShift D' ℤ]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D'] [CategoryTheory.IsTriangulated D']

/- The source's first K-injective derived-functor lemma is expressed using
   the canonical `rightDerivedDefined` and `ComputesRightDerived` predicates.
   `HasKInjectiveResolution` is the earlier chapter's source-facing package
   for a quasi-isomorphism towards a K-injective complex. -/
theorem kInjective_rightDerived_defined_and_computes
    (F : BookHomotopyCategory A ⥤ D')
    (hF : Nonempty (ExactTriangulatedFunctorData F)) :
    (∀ K : BookComplex A,
      HasKInjectiveResolution A K →
        rightDerivedDefined
          (quasiIsoHomotopyProperty A)
          (quasiIsoHomotopyProperty_properties A).1 F
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ∧
      (∀ I : BookComplex A, I.IsKInjective →
        ComputesRightDerived
          (quasiIsoHomotopyProperty A)
          (quasiIsoHomotopyProperty_properties A).1 F
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  sorry

/- The phrase `RF(I) = F(I)` is made precise by requiring the comparison
   component of a right derived functor to be an isomorphism on every
   K-injective complex. -/
theorem rightDerived_exists_of_enough_kInjectives
    (F : BookHomotopyCategory A ⥤ D')
    (hF : Nonempty (ExactTriangulatedFunctorData F))
    (hEnough : ∀ K : BookComplex A, HasKInjectiveResolution A K) :
    ∃ (RF : DerivedCategory A ⥤ D')
      (α : F ⟶ (DerivedCategory.Qh (C := A)) ⋙ RF),
      Functor.IsRightDerivedFunctor RF α (quasiIsoHomotopyProperty A) ∧
        ∀ I : BookComplex A, I.IsKInjective →
          IsIso
            (α.app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  sorry

end DerivedFunctor

/-! ## Split inverse systems -/

/- The source's inverse system is the positive-integer inverse system supplied
   by Homology, Chapter 31.  Its termwise split-surjection condition is the
   earlier `termwiseSplitSurjection` interface. -/
theorem inverseSystemLimit_isKInjective_of_split_surjective
    {A : Type u} [Category.{v} A] [Abelian A]
    (I : NatInverseSystem (BookComplex A))
    [∀ m : ℤ, HasLimit
      (I ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) m)]
    (hI : ∀ n : ℕ+, (I.obj (Opposite.op n)).IsKInjective)
    (hsplit : ∀ n : ℕ+,
      Formalization.Books.Derived.Unit09.termwiseSplitSurjection
        (successiveTransitionMap I n)) :
    (inverseSystemLimit I).IsKInjective := by
  sorry

/- The source notes that the split-tower lemma extends to larger ordinals;
   the earlier inverse-system chapter already exposes the ordinal-limit
   infrastructure.  The source also warns that combining the countable
   construction with bounded-below injective resolutions may fail to produce
   enough K-injectives; this warning is not an additional theorem. -/

/-! ## Exact adjoints preserve K-injectives -/

theorem additive_right_adjoint_preserves_isKInjective
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive]
    (adj : v ⊣ u)
    (hv : Formalization.Books.Categories.Unit23.IsExact v)
    {I : BookComplex A} (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  sorry

end Formalization.Books.Derived.Unit31
