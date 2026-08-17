import Formalization.Books.Algebra.Unit03.BasicNotions
import Formalization.Books.Algebra.Unit14.BaseChange
import Formalization.Books.Algebra.Unit70.BlowUpAlgebras
import Formalization.Books.MoreAlgebra.Unit30.KoszulRegularSequences
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.RingHom.Flat

/-!
# More on Algebra, Chapter 31: More on Koszul regular sequences

This chapter records the six statements in the source section.  The algebraic
Čech complex and the canonical homology base-change map are not present in the
project's Mathlib version, so their source-facing data are isolated in small
interfaces below.  All ring, quotient, tensor-product, blowup, regularity,
flatness, and smoothness constructions use the canonical APIs from earlier
chapters.
-/

namespace Formalization.Books.MoreAlgebra.Unit31

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Algebra.Unit14
open Formalization.Books.Algebra.Unit69
open Formalization.Books.MoreAlgebra.Unit30
open scoped TensorProduct

noncomputable section

universe u

/-! ## The extended alternating Čech complex -/

/-- Source-facing data for the extended alternating Čech complex associated to
a finite list.  The complex is the localization/direct-sum complex from the
source; its construction is not available in the current Mathlib API, so the
formula assertion is kept as an explicit field until that construction is
formalized. -/
structure ExtendedAlternatingCechComplexData
    (R : Type u) [CommRing R] (f : List R) where
  complex : CochainComplex (ModuleCat.{u} R) ℕ
  is_extended_alternating : Prop

/-- A cochain complex has cohomology only in the indicated degree. -/
def CohomologyOnlyInDegree
    {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) : Prop :=
  ∀ i : ℕ, i ≠ n → IsZero (C.homology i)

/-- A Koszul-regular list has extended alternating Čech cohomology only in
its top degree. -/
theorem vanishing_extended_alternating_koszul
    {R : Type u} [CommRing R] (f : List R)
    (C : ExtendedAlternatingCechComplexData R f)
    (hC : C.is_extended_alternating)
    (hf : IsKoszulRegular R f) :
    CohomologyOnlyInDegree C.complex f.length := by
  sorry

/-! ## The affine blowup presentation -/

/-- The ordered list of generators used by the finite-generator affine blowup
presentation: `a` followed by the remaining entries. -/
def blowupPresentationGenerators
    {R : Type u} [CommRing R] (a : R) (rest : List R) :
    Fin (rest.length + 1) → R :=
  fun i => (a :: rest).get i

/-- If `a, a₂, ..., aᵣ` is `H₁`-regular, the affine blowup at the ideal they
generate has the expected polynomial quotient presentation. -/
theorem blowup_regular_sequence_presentation
    {R : Type u} [CommRing R] (a : R) (rest : List R)
    (hreg : IsHOneRegular R (a :: rest)) :
    Nonempty
      (Formalization.Books.Algebra.Unit70.affineBlowup
          (Ideal.ofList (a :: rest)) a ≃+*
        MvPolynomial (Fin rest.length) R ⧸
          Formalization.Books.Algebra.Unit70.finiteGeneratorRelationIdeal
            rest.length (blowupPresentationGenerators a rest)) := by
  sorry

/-! ## Flat base change for first Koszul homology -/

/-- The quotient map induced by a list of elements. -/
def quotientMapOfList
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (xs : List B) :
    A →+* B ⧸ Ideal.ofList xs :=
  (Ideal.Quotient.mk (Ideal.ofList xs)).comp f

/-- Flatness of the quotient by a list over the source ring. -/
def quotientFlatOver
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (xs : List B) : Prop :=
  RingHom.Flat (quotientMapOfList f xs)

/-- The list obtained by applying the canonical map `B → B ⊗[A] A'` to a
sequence in `B`. -/
def baseChangedList
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A A' := g.toAlgebra
    List (B ⊗[A] A') := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A A' := g.toAlgebra
  exact xs.map (baseChangeAlgebraMap f g)

/-- The source and target modules of the canonical `H₁` base-change map. -/
noncomputable abbrev koszulHOneBaseChangeSource
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B) : ModuleCat.{u} A' :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A A' := g.toAlgebra
  (ModuleCat.extendScalars g).obj
    ((ModuleCat.restrictScalars f).obj
      ((koszulComplexOnListWithCoefficients B B xs).homology 1))

noncomputable abbrev koszulHOneBaseChangeTarget
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B) : ModuleCat.{u} A' :=
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A A' := g.toAlgebra
  (ModuleCat.restrictScalars (baseChangeRingMap f g)).obj
    ((koszulComplexOnListWithCoefficients (B ⊗[A] A') (B ⊗[A] A')
        (baseChangedList f g xs)).homology 1)

/-- Data for the canonical `H₁` base-change map. -/
structure KoszulHOneBaseChangeData
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B) where
  map : koszulHOneBaseChangeSource f g xs ⟶
    koszulHOneBaseChangeTarget f g xs
  surjective : Function.Surjective (fun x => map x)

/-- If `B/(f)` is flat over `A`, the canonical `H₁` base-change map is
surjective. -/
theorem base_change_HOne_surjective
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B)
    (hflat : quotientFlatOver f xs) :
    Nonempty (KoszulHOneBaseChangeData f g xs) := by
  sorry

/-- A chosen representative of the canonical `H₁` base-change map. -/
noncomputable def canonicalKoszulHOneBaseChangeData
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B)
    (hflat : quotientFlatOver f xs) :
    KoszulHOneBaseChangeData f g xs :=
  Classical.choice (base_change_HOne_surjective f g xs hflat)

/-- The canonical surjective `H₁` base-change map. -/
noncomputable def canonicalKoszulHOneBaseChangeMap
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B)
    (hflat : quotientFlatOver f xs) :
    koszulHOneBaseChangeSource f g xs ⟶
      koszulHOneBaseChangeTarget f g xs :=
  (canonicalKoszulHOneBaseChangeData f g xs hflat).map

theorem canonicalKoszulHOneBaseChangeMap_surjective
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B)
    (hflat : quotientFlatOver f xs) :
    Function.Surjective
      (fun x => canonicalKoszulHOneBaseChangeMap f g xs hflat x) :=
  (canonicalKoszulHOneBaseChangeData f g xs hflat).surjective

/-! ## Relative regularity after base change -/

/-- Quasi-regularity and `H₁`-regularity are preserved by this base change
when the quotient by the sequence is flat over the base. -/
theorem relative_regular_immersion_algebra
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    (f : A →+* B) (g : A →+* A') (xs : List B)
    (hflat : quotientFlatOver f xs) :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A A' := g.toAlgebra
    letI : Algebra A' (B ⊗[A] A') := (baseChangeRingMap f g).toAlgebra
    (Formalization.Books.Algebra.Unit69.IsQuasiRegular B xs →
        Formalization.Books.Algebra.Unit69.IsQuasiRegular
          (B ⊗[A] A') (baseChangedList f g xs)) ∧
      (IsHOneRegular B xs →
        IsHOneRegular (B ⊗[A] A') (baseChangedList f g xs)) := by
  sorry

/-! ## Cutting by a locally nilpotent ideal -/

/-- The base and target rings after cutting an `A'`-algebra by an ideal `I`. -/
abbrev cutBaseRing
    {A' : Type u} [CommRing A'] (I : Ideal A') := A' ⧸ I

abbrev cutTargetRing
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') :=
  B' ⧸ Ideal.map f I

/-- The canonical map from the cut base to the cut target. -/
noncomputable def cutQuotientMap
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') :
    cutBaseRing I →+* cutTargetRing f I :=
  Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map

/-- The image of a list in the cut target ring. -/
def cutImageList
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B') :
    List (cutTargetRing f I) :=
  xs.map (Ideal.Quotient.mk (Ideal.map f I))

/-- The map from the cut base to the quotient of the cut target by the image
of a list. -/
noncomputable def cutQuotientMapByList
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B') :
    cutBaseRing I →+*
      cutTargetRing f I ⧸ Ideal.ofList (cutImageList f I xs) :=
  (Ideal.Quotient.mk (Ideal.ofList (cutImageList f I xs))).comp
    (cutQuotientMap f I)

/-- Flatness of the cut quotient over the cut base. -/
def cutQuotientFlat
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B') : Prop :=
  RingHom.Flat (cutQuotientMapByList f I xs)

/-- Smoothness of the cut quotient over the cut base. -/
def cutQuotientSmooth
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B') : Prop :=
  RingHom.Smooth (cutQuotientMapByList f I xs)

/-- Flatness survives cutting by a locally nilpotent ideal under the
finite-presentation and quasi-regular hypotheses. -/
theorem cut_by_koszul_flat
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B')
    (hflat : RingHom.Flat f)
    (hfp : f.FinitePresentation)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquasi : Formalization.Books.Algebra.Unit69.IsQuasiRegular
      (cutTargetRing f I) (cutImageList f I xs))
    (hquotflat : cutQuotientFlat f I xs) :
    RingHom.Flat (quotientMapOfList f xs) := by
  sorry

/-- Smoothness survives the same cut when the quotient before cutting is
smooth over the cut base. -/
theorem cut_by_koszul
    {A' B' : Type u} [CommRing A'] [CommRing B']
    (f : A' →+* B') (I : Ideal A') (xs : List B')
    (hflat : RingHom.Flat f)
    (hfp : f.FinitePresentation)
    (hI : Formalization.Books.Algebra.Unit03.locallyNilpotentIdeal I)
    (hquasi : Formalization.Books.Algebra.Unit69.IsQuasiRegular
      (cutTargetRing f I) (cutImageList f I xs))
    (hsmooth : cutQuotientSmooth f I xs) :
    RingHom.Smooth (quotientMapOfList f xs) := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit31
