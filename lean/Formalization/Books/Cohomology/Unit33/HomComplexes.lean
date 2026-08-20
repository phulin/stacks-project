import Formalization.Books.Cohomology.Unit19.FlatResolutions
import Formalization.Books.Cohomology.Unit21.UnboundedComplexes
import Formalization.Books.Modules.Unit22.InternalHom
import Formalization.Books.Modules.Unit28.Differentials
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Cohomology of Sheaves, Chapter 33: Hom complexes

This file records the Hom-complex construction and the tensor--Hom,
restriction, derived, and K-injective interfaces from the source section.
The commutative sheaf-of-rings presentation is the tensor-compatible model
used by the preceding sheaf-module chapters.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open Opposite
open TopologicalSpace
open HomologicalComplex
open ComplexShape
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit22
open Formalization.Books.Cohomology.Unit19
open Formalization.Books.Sheaves.Unit20

universe v

namespace Formalization.Books.Cohomology.Unit33

/-! ## Ringed spaces, complexes, and their open restrictions -/

abbrev CommutativeRingedSpace :=
  Formalization.Books.Modules.Unit28.CommutativeRingedSpace

abbrev SheafModule (X : CommutativeRingedSpace.{v}) :=
  CommRingSheafModule X.structureSheaf

abbrev SheafComplex (X : CommutativeRingedSpace.{v}) :=
  CochainComplex (SheafModule X) ℤ

abbrev SheafHomotopy (X : CommutativeRingedSpace.{v}) :=
  HomotopyCategory (SheafModule X) (.up ℤ)

abbrev SheafDerived (X : CommutativeRingedSpace.{v}) :=
  DerivedCategory (SheafModule X)

noncomputable abbrev sheafDerivedQuotient (X : CommutativeRingedSpace.{v}) :
    SheafComplex X ⥤ SheafDerived X :=
  DerivedCategory.Q

noncomputable def openSpace
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    CommutativeRingedSpace.{v} :=
  { carrier := (Opens.toTopCat X.carrier).obj U
    structureSheaf :=
      Formalization.Books.Modules.Unit28.restrictCommRingSheaf U
        X.structureSheaf }

structure OpenRestrictionData
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) where
  restriction : SheafModule X ⥤ SheafModule (openSpace X U)
  restriction_additive : restriction.Additive

theorem exists_openRestrictionData
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    Nonempty (OpenRestrictionData X U) := by
  sorry

noncomputable def openRestrictionData
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    OpenRestrictionData X U :=
  Classical.choice (exists_openRestrictionData X U)

noncomputable def openRestrictionComplexFunctor
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    SheafComplex X ⥤ SheafComplex (openSpace X U) := by
  let D := openRestrictionData X U
  letI : D.restriction.Additive := D.restriction_additive
  exact D.restriction.mapHomologicalComplex (ComplexShape.up ℤ)

abbrev openSheafHomotopy
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :=
  SheafHomotopy (openSpace X U)

abbrev openSheafDerived
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :=
  SheafDerived (openSpace X U)

noncomputable abbrev openSheafDerivedQuotient
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    SheafComplex (openSpace X U) ⥤
      openSheafDerived X U :=
  DerivedCategory.Q

noncomputable abbrev openSheafHomotopyQuotient
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    SheafComplex (openSpace X U) ⥤
      openSheafHomotopy X U :=
  HomotopyCategory.quotient
    (SheafModule (openSpace X U)) (.up ℤ)

/-! ## The degreewise internal Hom and its differential -/

noncomputable def sheafHomTerm
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) (n : ℤ) : SheafModule X :=
  limit (Discrete.functor fun p : ℤ =>
    internalHom X.structureSheaf (L.X (p - n)) (M.X p))

noncomputable def sheafHomTermProjection
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) (n p : ℤ) :
    sheafHomTerm X L M n ⟶
      internalHom X.structureSheaf (L.X (p - n)) (M.X p) :=
  limit.π _ (Discrete.mk p)

structure SheafHomComplexData
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) where
  complex : SheafComplex X
  termIso : ∀ n : ℤ, complex.X n ≅ sheafHomTerm X L M n
  differential_formula : ∀ (n p : ℤ),
    complex.d n (n + 1) ≫ (termIso (n + 1)).hom ≫
        sheafHomTermProjection X L M (n + 1) p =
      (termIso n).hom ≫ sheafHomTermProjection X L M n (p - 1) ≫
          internalHomPostcomp (F := L.X ((p - 1) - n))
            (M.d (p - 1) p) ≫
            internalHomPrecomp (G := M.X p)
              (eqToHom (by congr 1; omega)) +
        (n + 1).negOnePow •
          ((termIso n).hom ≫ sheafHomTermProjection X L M n p ≫
            internalHomPrecomp (G := M.X p)
              (L.d (p - (n + 1)) (p - n)))

theorem exists_sheafHomComplexData
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) :
    Nonempty (SheafHomComplexData X L M) := by
  sorry

noncomputable def sheafHomComplexData
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) :
    SheafHomComplexData X L M :=
  Classical.choice (exists_sheafHomComplexData X L M)

noncomputable abbrev sheafHomComplex
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) : SheafComplex X :=
  (sheafHomComplexData X L M).complex

noncomputable def sheafHomComplex_degree_identification
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) (n : ℤ) :
    (sheafHomComplex X L M).X n ≅ sheafHomTerm X L M n :=
  (sheafHomComplexData X L M).termIso n

theorem sheafHomComplex_differential_formula
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) (n p : ℤ) :
    (sheafHomComplex X L M).d n (n + 1) ≫
        (sheafHomComplex_degree_identification X L M (n + 1)).hom ≫
        sheafHomTermProjection X L M (n + 1) p =
      (sheafHomComplex_degree_identification X L M n).hom ≫
          sheafHomTermProjection X L M n (p - 1) ≫
            internalHomPostcomp (F := L.X ((p - 1) - n))
              (M.d (p - 1) p) ≫
              internalHomPrecomp (G := M.X p)
                (eqToHom (by congr 1; omega)) +
        (n + 1).negOnePow •
          ((sheafHomComplex_degree_identification X L M n).hom ≫
            sheafHomTermProjection X L M n p ≫
              internalHomPrecomp (G := M.X p)
                (L.d (p - (n + 1)) (p - n))) := by
  sorry

theorem sheafHomComplex_differential_squared
    (X : CommutativeRingedSpace.{v})
    (L M : SheafComplex X) (n m p : ℤ) :
    (sheafHomComplex X L M).d n m ≫
        (sheafHomComplex X L M).d m p = 0 :=
  (sheafHomComplex X L M).d_comp_d n m p

/-! ## Sections and the cohomology identification -/

noncomputable def sheafSectionsComplexFunctor
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier) :
    SheafComplex X ⥤
      CochainComplex
        (ModuleCat.{v} (X.structureSheaf.obj.obj (op U))) ℤ := by
  let F := SheafOfModules.evaluation
    (commRingSheafToRingSheaf X.structureSheaf) (op U)
  letI : F.Additive := by sorry
  exact F.mapHomologicalComplex (ComplexShape.up ℤ)

theorem cohomology_hom_complex_equiv_exists
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier)
    (L M : SheafComplex X) (n : ℤ) :
    Nonempty (((sheafSectionsComplexFunctor X U).obj
        (sheafHomComplex X L M)).homology n ≃+
      ((openSheafHomotopyQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj L) ⟶
        (shiftFunctor (openSheafHomotopy X U) n).obj
          ((openSheafHomotopyQuotient X U).obj
            ((openRestrictionComplexFunctor X U).obj M)))) := by
  sorry

noncomputable def cohomology_hom_complex_equiv
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier)
    (L M : SheafComplex X) (n : ℤ) :
    ((sheafSectionsComplexFunctor X U).obj
        (sheafHomComplex X L M)).homology n ≃+
      ((openSheafHomotopyQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj L) ⟶
        (shiftFunctor (openSheafHomotopy X U) n).obj
          ((openSheafHomotopyQuotient X U).obj
            ((openRestrictionComplexFunctor X U).obj M))) :=
  Classical.choice (cohomology_hom_complex_equiv_exists X U L M n)

/-! ## Canonical tensor--Hom maps -/

noncomputable abbrev sheafTensorComplex
    (X : CommutativeRingedSpace.{v})
    (K L : SheafComplex X) : SheafComplex X :=
  Formalization.Books.Cohomology.Unit19.sheafTensorComplex K L

theorem sheafHomComposeIso_exists
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    Nonempty (sheafHomComplex X K (sheafHomComplex X L M) ≅
      sheafHomComplex X (sheafTensorComplex X K L) M) := by
  sorry

noncomputable def sheafHomComposeIso
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    sheafHomComplex X K (sheafHomComplex X L M) ≅
      sheafHomComplex X (sheafTensorComplex X K L) M :=
  Classical.choice (sheafHomComposeIso_exists X K L M)

theorem sheafHomComposition_exists
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    Nonempty (sheafTensorComplex X (sheafHomComplex X L M)
        (sheafHomComplex X K L) ⟶ sheafHomComplex X K M) := by
  sorry

noncomputable def sheafHomComposition
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    sheafTensorComplex X (sheafHomComplex X L M)
        (sheafHomComplex X K L) ⟶ sheafHomComplex X K M :=
  Classical.choice (sheafHomComposition_exists X K L M)

theorem sheafHomDiagonalBetter_exists
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    Nonempty (sheafTensorComplex X K (sheafHomComplex X M L) ⟶
      sheafHomComplex X M (sheafTensorComplex X K L)) := by
  sorry

noncomputable def sheafHomDiagonalBetter
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    sheafTensorComplex X K (sheafHomComplex X M L) ⟶
      sheafHomComplex X M (sheafTensorComplex X K L) :=
  Classical.choice (sheafHomDiagonalBetter_exists X K L M)

theorem sheafHomDiagonal_exists
    (X : CommutativeRingedSpace.{v})
    (K L : SheafComplex X) :
    Nonempty (K ⟶ sheafHomComplex X L (sheafTensorComplex X K L)) := by
  sorry

noncomputable def sheafHomDiagonal
    (X : CommutativeRingedSpace.{v})
    (K L : SheafComplex X) :
    K ⟶ sheafHomComplex X L (sheafTensorComplex X K L) :=
  Classical.choice (sheafHomDiagonal_exists X K L)

theorem sheafHomEvaluate_exists
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    Nonempty (sheafTensorComplex X (sheafHomComplex X L M) K ⟶
      sheafHomComplex X (sheafHomComplex X K L) M) := by
  sorry

noncomputable def sheafHomEvaluate
    (X : CommutativeRingedSpace.{v})
    (K L M : SheafComplex X) :
    sheafTensorComplex X (sheafHomComplex X L M) K ⟶
      sheafHomComplex X (sheafHomComplex X K L) M :=
  Classical.choice (sheafHomEvaluate_exists X K L M)

/-! ## Derived Hom interfaces -/

theorem sheafHomIntoKInjective_exists
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier)
    (L I : SheafComplex X) (hI : I.IsKInjective) :
    Nonempty (((sheafSectionsComplexFunctor X U).obj
        (sheafHomComplex X L I)).homology 0 ≃+
      ((openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj L) ⟶
        (openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj I))) := by
  sorry

noncomputable def sheafHomIntoKInjective
    (X : CommutativeRingedSpace.{v}) (U : Opens X.carrier)
    (L I : SheafComplex X) (hI : I.IsKInjective) :
    ((sheafSectionsComplexFunctor X U).obj
        (sheafHomComplex X L I)).homology 0 ≃+
      ((openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj L) ⟶
        (openSheafDerivedQuotient X U).obj
          ((openRestrictionComplexFunctor X U).obj I)) :=
  Classical.choice (sheafHomIntoKInjective_exists X U L I hI)

theorem sheafHomWellDefined_exists
    (X : CommutativeRingedSpace.{v})
    {I I' L L' : SheafComplex X}
    (fI : I' ⟶ I) (fL : L' ⟶ L)
    (hI : QuasiIso fI) (hL : QuasiIso fL)
    (hI' : I'.IsKInjective) (hI0 : I.IsKInjective) :
    Nonempty {f : sheafHomComplex X L I' ⟶ sheafHomComplex X L' I //
      QuasiIso f} := by
  sorry

noncomputable def sheafHomWellDefinedMap
    (X : CommutativeRingedSpace.{v})
    {I I' L L' : SheafComplex X}
    (fI : I' ⟶ I) (fL : L' ⟶ L)
    (hI : QuasiIso fI) (hL : QuasiIso fL)
    (hI' : I'.IsKInjective) (hI0 : I.IsKInjective) :
    sheafHomComplex X L I' ⟶ sheafHomComplex X L' I :=
  (Classical.choice
    (sheafHomWellDefined_exists X fI fL hI hL hI' hI0)).1

theorem sheafHomWellDefinedMap_isQuasiIso
    (X : CommutativeRingedSpace.{v})
    {I I' L L' : SheafComplex X}
    (fI : I' ⟶ I) (fL : L' ⟶ L)
    (hI : QuasiIso fI) (hL : QuasiIso fL)
    (hI' : I'.IsKInjective) (hI0 : I.IsKInjective) :
    QuasiIso (sheafHomWellDefinedMap X fI fL hI hL hI' hI0) :=
  (Classical.choice
    (sheafHomWellDefined_exists X fI fL hI hL hI' hI0)).2

theorem sheafHomFromKFlatIntoKInjective_isKInjective
    (X : CommutativeRingedSpace.{v})
    (L I : SheafComplex X) (hL : IsKFlat L)
    (hI : I.IsKInjective) :
    (sheafHomComplex X L I).IsKInjective := by
  sorry

end Formalization.Books.Cohomology.Unit33
