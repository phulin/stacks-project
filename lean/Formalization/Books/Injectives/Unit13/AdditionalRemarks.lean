import Formalization.Books.Injectives.Unit12.KInjectivesInGrothendieckCategories
import Formalization.Books.Homology.Unit15.TruncationOfComplexes
import Formalization.Books.Homology.Unit20.FilteredComplexes
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Yoneda

/-!
# Injectives, Chapter 13: additional remarks on Grothendieck abelian categories

This file records the precise interfaces in the source section.  The
representability and filtered-complex constructions use the canonical
`Functor.IsRepresentable`, `DerivedCategory`, K-injective, filtered-complex,
and spectral-sequence APIs.  Proofs of the folklore existence results are
deferred to the proof stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit20
open scoped BigOperators ZeroObject

universe u v w u' v'

namespace Formalization.Books.Injectives.Unit13

/-! ## Representability and products -/

/- A contravariant functor preserves colimits in `C` precisely when it
preserves limits after viewing the colimit diagram in `Cᵒᵖ`.  The latter is
Mathlib's canonical preservation predicate. -/
abbrev CommutesWithColimits {C : Type u} [Category.{v} C]
    (F : Cᵒᵖ ⥤ Type v) : Prop :=
  PreservesLimits F

/- The Yoneda representability predicate is deliberately not duplicated. -/
theorem grothendieck_brown
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (F : Cᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ CommutesWithColimits F := by
  sorry

/- The source calls this AB3*.  `HasProducts` is the established Mathlib
interface for arbitrary products, so no parallel class is introduced. -/
instance grothendieck_has_products
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] :
    HasProducts.{v} C := by
  sorry

/- A precise version of the size warning in the source remark.  The
derived-category universe is explicit in Mathlib; the theorem below records
the additional smallness conclusion supplied by K-injective replacements. -/
def DerivedHomSetsAreSmall
    (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : Prop :=
  ∀ K L : DerivedCategory C, Small.{w} (K ⟶ L)

theorem grothendieck_derived_hom_sets_are_small
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C] :
    DerivedHomSetsAreSmall C := by
  sorry

theorem grothendieck_has_derived_category
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C] :
    Nonempty (HasDerivedCategory.{max u v} C) :=
  ⟨HasDerivedCategory.standard C⟩

theorem module_category_is_grothendieck_abelian
    (R : Type v) [Ring R] :
    IsGrothendieckAbelian.{v} (ModuleCat.{v} R) := by
  infer_instance

/- The source's examples, module categories and sheaves of modules on a
   ringed site, are already supplied by the earlier Injectives chapters and
   Mathlib category instances; this section introduces no duplicate example
   categories. -/

structure DerivedHomKInjectiveComparison
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) where
  resolution : Formalization.Books.Injectives.Unit12.KInjectiveEmbedding L
  hom_equiv : ((DerivedCategory.Q (C := C)).obj K ⟶
      (DerivedCategory.Q (C := C)).obj L) ≃
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj resolution.target)

theorem derived_hom_is_computed_by_K_injective
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (K L : CochainComplex C ℤ) :
    Nonempty (DerivedHomKInjectiveComparison K L) := by
  sorry

/-! ## Products and direct sums in derived categories -/

noncomputable def derivedObjectOfComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : CochainComplex C ℤ) : DerivedCategory C :=
  (DerivedCategory.Q (C := C)).obj K

noncomputable def termwiseDirectSumComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {I : Type w} [HasCoproductsOfShape I C]
    (K : I → CochainComplex C ℤ) : CochainComplex C ℤ :=
  ∐ K

noncomputable def termwiseProductComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    {I : Type w} [HasProductsOfShape I C]
    (K : I → CochainComplex C ℤ) : CochainComplex C ℤ :=
  ∏ᶜ K

noncomputable def derivedDirectSumCofan
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {I : Type w}
    [HasCoproductsOfShape I C]
    (K : I → CochainComplex C ℤ) :
    Cofan (fun i => derivedObjectOfComplex (K i)) :=
  Cofan.mk (derivedObjectOfComplex (termwiseDirectSumComplex K))
    (fun i =>
      (DerivedCategory.Q (C := C)).map (Sigma.ι K i))

noncomputable def derivedProductFan
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {I : Type w}
    [HasProductsOfShape I C]
    (K : I → CochainComplex C ℤ) :
    Fan (fun i => derivedObjectOfComplex (K i)) :=
  Fan.mk (derivedObjectOfComplex (termwiseProductComplex K))
    (fun i =>
      (DerivedCategory.Q (C := C)).map (Pi.π K i))

theorem derived_direct_sums_and_products
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C] :
    HasCoproducts (DerivedCategory C) ∧ HasProducts (DerivedCategory C) := by
  sorry

theorem derived_termwise_direct_sum_is_coproduct
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C] {I : Type w}
    [HasCoproductsOfShape I C]
    (K : I → CochainComplex C ℤ) :
    Nonempty (IsColimit (derivedDirectSumCofan K)) := by
  sorry

theorem derived_termwise_product_of_K_injectives_is_product
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C] {I : Type w}
    [HasProductsOfShape I C]
    (K : I → CochainComplex C ℤ)
    (hK : ∀ i, (K i).IsKInjective) :
    Nonempty (IsLimit (derivedProductFan K)) := by
  sorry

noncomputable def shiftedSingleDerivedObject
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : C) (n : ℤ) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C n).obj M

structure KInjectiveShiftedFamily
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : ℤ → C) where
  complex : ℤ → CochainComplex C ℤ
  represents : ∀ n : ℤ, Nonempty (derivedObjectOfComplex (complex n) ≅
    shiftedSingleDerivedObject (M n) n)
  KInjective : ∀ n : ℤ, (complex n).IsKInjective

structure DerivedShiftedFamilySumProduct
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{0} C] [HasCoproductsOfShape ℤ C]
    [HasProductsOfShape ℤ C]
    (M : ℤ → C)
    (F : @KInjectiveShiftedFamily C _ _ _ M) where
  direct_sum : Nonempty (IsColimit
    (derivedDirectSumCofan (C := C) (I := ℤ) F.complex))
  product : Nonempty (IsLimit
    (derivedProductFan (C := C) (I := ℤ) F.complex))
  direct_sum_product_iso : Nonempty (derivedObjectOfComplex (C := C)
    (termwiseDirectSumComplex (C := C) (I := ℤ) F.complex) ≅
    derivedObjectOfComplex (C := C)
      (termwiseProductComplex (C := C) (I := ℤ) F.complex))

theorem derived_shifted_family_is_direct_sum_and_product
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{0} C] [AB4Star C]
    (M : ℤ → C) (F : @KInjectiveShiftedFamily C _ _ _ M) :
    Nonempty (DerivedShiftedFamilySumProduct M F) := by
  sorry

/-! ## Derived limits and right-derived functors -/

abbrev SequentialInverseSystem (D : Type u') [Category.{v'} D] :=
  ℕᵒᵖ ⥤ D

def inverseSystemTransition
    {D : Type u'} [Category.{v'} D]
    (F : SequentialInverseSystem D) (n : ℕ) :
    F.obj (Opposite.op (n + 1)) ⟶ F.obj (Opposite.op n) :=
  F.map (opHomOfLE (Nat.le_succ n))

structure ProductPresentation
    {D : Type u'} [Category.{v'} D]
    (F : SequentialInverseSystem D) where
  product : D
  projection : ∀ n : ℕ, product ⟶ F.obj (Opposite.op n)
  isLimit : IsLimit (Fan.mk product projection)

def inverseSystemDifferenceMap
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    (F : SequentialInverseSystem D) (P : ProductPresentation F) :
    P.product ⟶ P.product :=
  P.isLimit.lift (Fan.mk P.product (fun n =>
    P.projection n - P.projection (n + 1) ≫ inverseSystemTransition F n))

structure DerivedLimitPresentation
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : SequentialInverseSystem D) (L : D) where
  product : ProductPresentation F
  inclusion : L ⟶ product.product
  connecting : product.product ⟶ (shiftFunctor D (1 : ℤ)).obj L
  distinguished :
    Triangle.mk inclusion (inverseSystemDifferenceMap F product) connecting ∈
      distTriang D

def IsDerivedLimit
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : SequentialInverseSystem D) (L : D) : Prop :=
  Nonempty (DerivedLimitPresentation F L)

structure RightDerivedFunctorData
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  computes_on_KInjectives :
    ∀ (I : CochainComplex A ℤ), I.IsKInjective →
      Nonempty (functor.obj (derivedObjectOfComplex I) ≅
        derivedObjectOfComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))

def CommutesWithDerivedLimits
    {D : Type u} [Category.{v} D] {E : Type u'} [Category.{v'} E]
    [Preadditive D] [Preadditive E] [HasZeroObject D] [HasZeroObject E]
    [HasShift D ℤ] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated D] [Pretriangulated E]
    (RF : D ⥤ E) : Prop :=
  ∀ (F : SequentialInverseSystem D) (L : D),
    IsDerivedLimit F L → IsDerivedLimit (F ⋙ RF) (RF.obj L)

theorem rightDerived_commutes_with_derived_limits
    {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    [IsGrothendieckAbelian.{max u v} A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasCountableProducts B] [CountableAB4Star B]
    (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (R : RightDerivedFunctorData F) :
    CommutesWithDerivedLimits R.functor := by
  sorry

/-! ## Filtered K-injective embeddings -/

abbrev FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] :=
  Formalization.Books.Homology.Unit20.FilteredComplex C

noncomputable def filteredComplexUnderlyingMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) :
    filteredComplexUnderlying K ⟶ filteredComplexUnderlying L :=
  ((filteredComplexForgetful (C := C)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

noncomputable def filteredComplexStepMap
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredComplex C} (f : K ⟶ L) (p : ℤ) :
    filteredComplexStepComplex K p ⟶ filteredComplexStepComplex L p :=
  ((filteredComplexStepFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.up ℤ)).map f

noncomputable def filteredComplexQuotientComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) : CochainComplex C ℤ :=
  cokernel (filteredComplexStepToUnderlying K p)

/- For the decreasing filtration used by the preceding Homology chapter,
   `p' ≤ p` gives `F^p ⟶ F^p'`; hence the well-typed subquotient is
   `F^p'/F^p`, correcting the reversed quotient notation in the source. -/
noncomputable def filteredComplexSubquotientComplex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p p' : ℤ) (hp' : p' ≤ p) :
  CochainComplex C ℤ :=
  cokernel (filteredComplexStepInclusion K p' p hp')

noncomputable def filteredComplexSubquotientProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p p' : ℤ) (hp' : p' ≤ p) :
    filteredComplexStepComplex K p' ⟶
      filteredComplexSubquotientComplex K p p' hp' :=
  cokernel.π (filteredComplexStepInclusion K p' p hp')

noncomputable def filteredComplexQuotientProjection
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (p : ℤ) :
    filteredComplexUnderlying K ⟶ filteredComplexQuotientComplex K p :=
  cokernel.π (filteredComplexStepToUnderlying K p)

noncomputable def filteredObjectStepInclusion
    {C : Type u} [Category.{v} C]
    (A : FilteredObject C) (p p' : ℤ) (hp' : p' ≤ p) :
    (A.filtration.obj p : C) ⟶ (A.filtration.obj p' : C) :=
  Subobject.ofLE (A.filtration.obj p) (A.filtration.obj p')
    (A.filtration.antitone hp')

structure FilteredKInjectiveEmbedding
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (K : FilteredComplex C) where
  target : FilteredComplex C
  map : K ⟶ target
  map_quasiIso : QuasiIso (filteredComplexUnderlyingMap map)
  map_termwise_mono : ∀ n : ℤ, Mono ((filteredComplexUnderlyingMap map).f n)
  target_terms_injective : ∀ n : ℤ, Injective ((target.X n).carrier)
  target_filtration_steps_injective :
    ∀ (n p : ℤ), Injective ((target.X n).filtration.obj p : C)
  target_quotients_injective :
    ∀ (n p : ℤ), Injective (cokernel ((target.X n).filtration.obj p).arrow)
  target_subquotients_injective :
    ∀ (n p p' : ℤ) (hp' : p' ≤ p),
      Injective (cokernel (filteredObjectStepInclusion (target.X n) p p' hp'))
  target_KInjective : (filteredComplexUnderlying target).IsKInjective
  target_steps_KInjective :
    ∀ p : ℤ, (filteredComplexStepComplex target p).IsKInjective
  target_quotients_KInjective :
    ∀ p : ℤ, (filteredComplexQuotientComplex target p).IsKInjective
  target_subquotients_KInjective :
    ∀ (p p' : ℤ) (hp' : p' ≤ p),
      (filteredComplexSubquotientComplex target p p' hp').IsKInjective
  step_quasiIso : ∀ p : ℤ, QuasiIso (filteredComplexStepMap map p)
  quotient_quasiIso :
    ∀ p : ℤ, ∃ q : filteredComplexQuotientComplex K p ⟶
      filteredComplexQuotientComplex target p,
      filteredComplexQuotientProjection K p ≫ q =
        filteredComplexUnderlyingMap map ≫
          filteredComplexQuotientProjection target p ∧ QuasiIso q
  subquotient_quasiIso :
    ∀ (p p' : ℤ) (hp' : p' ≤ p),
      ∃ q : filteredComplexSubquotientComplex K p p' hp' ⟶
        filteredComplexSubquotientComplex target p p' hp',
        filteredComplexSubquotientProjection K p p' hp' ≫ q =
          filteredComplexStepMap map p' ≫
            filteredComplexSubquotientProjection target p p' hp' ∧
          QuasiIso q

theorem filtered_K_injective_embedding
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    (K : FilteredComplex C) :
    Nonempty (FilteredKInjectiveEmbedding K) := by
  sorry

/- The source warns that the auxiliary maps `sᵖ` need not satisfy
`tᵖ = αᵖ ≫ sᵖ`; the interface above intentionally assumes no such
   identification. -/

/-! ## Ext groups and spectral-sequence interfaces -/

abbrev ExtGroup
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasShift D ℤ]
    (M N : D) (n : ℤ) : Type _ :=
  M ⟶ (shiftFunctor D n).obj N

noncomputable def ExtGroupObject
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasShift D ℤ]
    (M N : D) (n : ℤ) : AddCommGrpCat :=
  AddCommGrpCat.of (ExtGroup M N n)

def extMap
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    {M N N' : D} (f : N ⟶ N') (n : ℤ) :
    ExtGroup M N n → ExtGroup M N' n :=
  fun g => g ≫ (shiftFunctor D n).map f

def extMapFromFirstVariable
    {D : Type u'} [Category.{v'} D] [Preadditive D]
    [HasShift D ℤ] {M M' N : D} (f : M' ⟶ M) (n : ℤ) :
    ExtGroup M N n → ExtGroup M' N n :=
  fun g => f ≫ g

def IsBoundedBelowComplex
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : CochainComplex C ℤ) : Prop :=
  ∃ n : ℤ, ∀ m : ℤ, m < n → IsZero (K.X m)

def IsBoundedAboveComplex
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : CochainComplex C ℤ) : Prop :=
  ∃ n : ℤ, ∀ m : ℤ, n < m → IsZero (K.X m)

def IsBoundedAboveDerived
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : DerivedCategory C) : Prop :=
  ∃ n : ℤ, ∀ m : ℤ, n < m →
    IsZero ((DerivedCategory.homologyFunctor C m).obj K)

def IsBoundedBelowDerived
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (K : DerivedCategory C) : Prop :=
  ∃ n : ℤ, ∀ m : ℤ, m < n →
    IsZero ((DerivedCategory.homologyFunctor C m).obj K)

noncomputable def canonicalCohomologyPiece
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℤ) (n : ℤ) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C n).obj
    ((DerivedCategory.homologyFunctor C n).obj
      (derivedObjectOfComplex K))

noncomputable def derivedSingleObject
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : C) : DerivedCategory C :=
  (DerivedCategory.singleFunctor C 0).obj M

def ExtIntoFiltrationCondition
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : DerivedCategory C)
    (K : FilteredComplex C) : Prop :=
  ∀ n : ℤ,
    (∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      ∀ g : ExtGroup M (derivedObjectOfComplex
        (filteredComplexStepComplex K p)) n, g = 0) ∧
    (∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      Function.Bijective (extMap (M := M)
        (N := derivedObjectOfComplex (filteredComplexStepComplex K p))
        (N' := derivedObjectOfComplex (filteredComplexUnderlying K))
        (DerivedCategory.Q.map (filteredComplexStepToUnderlying K p)) n))

def ExtFromFiltrationCondition
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] (M : FilteredComplex C)
    (K : DerivedCategory C) : Prop :=
  ∀ n : ℤ,
    (∃ p₀ : ℤ, ∀ p : ℤ, p ≤ p₀ →
      ∀ g : ExtGroup (derivedObjectOfComplex
        (filteredComplexQuotientComplex M p)) K n, g = 0) ∧
    (∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      Function.Bijective (extMapFromFirstVariable
        (M := derivedObjectOfComplex
          (filteredComplexQuotientComplex M p))
        (M' := derivedObjectOfComplex (filteredComplexUnderlying M))
        (N := K)
        (DerivedCategory.Q.map (filteredComplexQuotientProjection M p)) n))

structure ExtAbutmentData
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
    (M N : D) where
  abutment : ℤ → AddCommGrpCat
  filtration : ∀ n : ℤ,
    DecreasingFiltration AddCommGrpCat (abutment n)
  abutment_iso : ∀ n : ℤ,
    Nonempty (abutment n ≅ ExtGroupObject M N n)

structure ExtSpectralSequenceData
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
    (M N : D) (page_index : ℕ) (E₁ : ℤ → ℤ → AddCommGrpCat) where
  model : FilteredComplex AddCommGrpCat
  sequence : FilteredComplexSpectralSequence model
  page_iso : ∀ p q : ℤ,
    Nonempty (sequence.page page_index (p, q) ≅ E₁ p q)
  bounded : ∀ (r : ℕ) (n : ℤ), ∃ a b : ℤ, ∀ p q : ℤ,
    p + q = n → (p < a ∨ b < p) → IsZero (sequence.page r (p, q))
  convergence : ExtAbutmentData M N

def ExtSpectralSequencePagewiseEquivalentTo
    {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
    {M₁ M₂ N₁ N₂ : D} {r₁ r₂ : ℕ} {E₁ E₂ : ℤ → ℤ → AddCommGrpCat}
    (S : ExtSpectralSequenceData M₁ N₁ r₁ E₁)
    (T : ExtSpectralSequenceData M₂ N₂ r₂ E₂) : Prop :=
  ∀ (r : ℕ) (p q : ℤ), Nonempty
    (S.sequence.page r (p, q) ≅ T.sequence.page r (p, q))

theorem ext_into_filtered_complex_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (K : FilteredComplex C)
    (hK : ExtIntoFiltrationCondition M K) :
    Nonempty (ExtSpectralSequenceData M
      (derivedObjectOfComplex (filteredComplexUnderlying K))
      1
      (fun p q => ExtGroupObject M
        (derivedObjectOfComplex (filteredComplexGradedPiece K p)) (p + q))) := by
  sorry

theorem ext_from_filtered_complex_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : FilteredComplex C) (K : DerivedCategory C)
    (hM : ExtFromFiltrationCondition M K) :
    Nonempty (ExtSpectralSequenceData
      (derivedObjectOfComplex (filteredComplexUnderlying M)) K
      1
      (fun p q => ExtGroupObject
        (derivedObjectOfComplex (filteredComplexGradedPiece M (-p))) K (p + q))) := by
  sorry

theorem ext_spectral_sequence_truncation_E₁
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (K : CochainComplex C ℤ)
    (hM : IsBoundedAboveDerived M)
    (hK : IsBoundedBelowDerived (derivedObjectOfComplex K)) :
    Nonempty (ExtSpectralSequenceData M (derivedObjectOfComplex K) 1
      (fun p q => ExtGroupObject M
        (canonicalCohomologyPiece K (-p)) (2 * p + q))) := by
  sorry

theorem ext_spectral_sequence_truncation_E₂
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (K : CochainComplex C ℤ)
    (hM : IsBoundedAboveDerived M)
    (hK : IsBoundedBelowDerived (derivedObjectOfComplex K)) :
    Nonempty (ExtSpectralSequenceData M (derivedObjectOfComplex K) 2
      (fun i j => ExtGroupObject M (canonicalCohomologyPiece K j) i)) := by
  sorry

theorem ext_spectral_sequence_truncation_independent_of_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (K₁ K₂ : CochainComplex C ℤ)
    (h₁₂ : Nonempty (derivedObjectOfComplex K₁ ≅
      derivedObjectOfComplex K₂)) :
    ∀ (S₁ : ExtSpectralSequenceData M (derivedObjectOfComplex K₁) 1
        (fun p q => ExtGroupObject M (canonicalCohomologyPiece K₁ (-p))
          (2 * p + q)))
      (S₂ : ExtSpectralSequenceData M (derivedObjectOfComplex K₂) 1
        (fun p q => ExtGroupObject M (canonicalCohomologyPiece K₂ (-p))
          (2 * p + q))),
      ExtSpectralSequencePagewiseEquivalentTo S₁ S₂ := by
  sorry

theorem ext_spectral_sequence_stupid_filtration
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : DerivedCategory C) (K : CochainComplex C ℤ)
    (hM : IsBoundedAboveDerived M)
    (hK : IsBoundedBelowComplex K) :
    Nonempty (ExtSpectralSequenceData M (derivedObjectOfComplex K) 1
      (fun p q => ExtGroupObject M (derivedSingleObject (K.X p)) q)) := by
  sorry

theorem ext_spectral_sequence_truncation_from_E₁
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : CochainComplex C ℤ) (K : DerivedCategory C)
    (hM : IsBoundedAboveDerived (derivedObjectOfComplex M))
    (hK : IsBoundedBelowDerived K) :
    Nonempty (ExtSpectralSequenceData (derivedObjectOfComplex M) K 1
      (fun p q => ExtGroupObject
        (canonicalCohomologyPiece M p) K (2 * p + q))) := by
  sorry

theorem ext_spectral_sequence_truncation_from_E₂
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : CochainComplex C ℤ) (K : DerivedCategory C)
    (hM : IsBoundedAboveDerived (derivedObjectOfComplex M))
    (hK : IsBoundedBelowDerived K) :
    Nonempty (ExtSpectralSequenceData (derivedObjectOfComplex M) K 2
      (fun i j => ExtGroupObject
        (canonicalCohomologyPiece M (-j)) K i)) := by
  sorry

theorem ext_spectral_sequence_truncation_from_independent_of_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M₁ M₂ : CochainComplex C ℤ) (K : DerivedCategory C)
    (h₁₂ : Nonempty (derivedObjectOfComplex M₁ ≅
      derivedObjectOfComplex M₂)) :
    ∀ (S₁ : ExtSpectralSequenceData (derivedObjectOfComplex M₁) K 1
        (fun p q => ExtGroupObject (canonicalCohomologyPiece M₁ p) K
          (2 * p + q)))
      (S₂ : ExtSpectralSequenceData (derivedObjectOfComplex M₂) K 1
        (fun p q => ExtGroupObject (canonicalCohomologyPiece M₂ p) K
          (2 * p + q))),
      ExtSpectralSequencePagewiseEquivalentTo S₁ S₂ := by
  sorry

theorem ext_spectral_sequence_stupid_filtration_from
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    (M : CochainComplex C ℤ) (K : DerivedCategory C)
    (hM : IsBoundedAboveComplex M)
    (hK : IsBoundedBelowDerived K) :
    Nonempty (ExtSpectralSequenceData (derivedObjectOfComplex M) K 1
      (fun p q => ExtGroupObject
        (derivedSingleObject (M.X (-p))) K q)) := by
  sorry

/-! ## Filtered and bifiltered representatives of inverse systems -/

structure DerivedInverseSystemWithMap
    {D : Type u'} [Category.{v'} D]
    (E : D) where
  system : ℤᵒᵖ ⥤ D
  to_limit : ∀ i : ℤ, system.obj (Opposite.op i) ⟶ E
  compatible : ∀ {i j : ℤ} (hij : i ≤ j),
    system.map (opHomOfLE hij) ≫ to_limit i = to_limit j

structure FilteredComplexRepresentsSystem
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    {E : DerivedCategory C}
    (S : DerivedInverseSystemWithMap E) where
  complex : FilteredComplex C
  object_iso : derivedObjectOfComplex
    (filteredComplexUnderlying complex) ≅ E
  step_iso : ∀ i : ℤ, derivedObjectOfComplex
    (filteredComplexStepComplex complex i) ≅
      S.system.obj (Opposite.op i)
  object_compatibility : ∀ i : ℤ,
    (DerivedCategory.Q.map (filteredComplexStepToUnderlying complex i)) ≫
        object_iso.hom =
      (step_iso i).hom ≫ S.to_limit i
  step_compatibility : ∀ {i j : ℤ} (hij : i ≤ j),
    (DerivedCategory.Q.map (filteredComplexStepInclusion complex i j hij)) ≫
        (step_iso i).hom =
      (step_iso j).hom ≫ S.system.map (opHomOfLE hij)

theorem represent_inverse_system_by_filtered_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    {E : DerivedCategory C}
    (S : DerivedInverseSystemWithMap E) :
    Nonempty (FilteredComplexRepresentsSystem S) := by
  sorry

structure BiFilteredComplex
    (C : Type u) [Category.{v} C] [Abelian C] where
  first : FilteredComplex C
  second : FilteredComplex C
  same_underlying : Nonempty (filteredComplexUnderlying first ≅
    filteredComplexUnderlying second)

structure BiFilteredComplexRepresentsSystems
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C]
    {E : DerivedCategory C}
    (S T : DerivedInverseSystemWithMap E) where
  complex : BiFilteredComplex C
  object_iso : derivedObjectOfComplex
    (filteredComplexUnderlying complex.first) ≅ E
  second_object_iso : derivedObjectOfComplex
    (filteredComplexUnderlying complex.second) ≅ E
  first_step_iso : ∀ i : ℤ, derivedObjectOfComplex
    (filteredComplexStepComplex complex.first i) ≅
      S.system.obj (Opposite.op i)
  second_step_iso : ∀ i : ℤ, derivedObjectOfComplex
    (filteredComplexStepComplex complex.second i) ≅
      T.system.obj (Opposite.op i)
  first_object_compatibility : ∀ i : ℤ,
    (DerivedCategory.Q.map
      (filteredComplexStepToUnderlying complex.first i)) ≫ object_iso.hom =
      (first_step_iso i).hom ≫ S.to_limit i
  second_object_compatibility : ∀ i : ℤ,
    (DerivedCategory.Q.map
      (filteredComplexStepToUnderlying complex.second i)) ≫
        second_object_iso.hom =
      (second_step_iso i).hom ≫ T.to_limit i
  first_compatibility : ∀ {i j : ℤ} (hij : i ≤ j),
    (DerivedCategory.Q.map
      (filteredComplexStepInclusion complex.first i j hij)) ≫
        (first_step_iso i).hom =
      (first_step_iso j).hom ≫ S.system.map (opHomOfLE hij)
  second_compatibility : ∀ {i j : ℤ} (hij : i ≤ j),
    (DerivedCategory.Q.map
      (filteredComplexStepInclusion complex.second i j hij)) ≫
        (second_step_iso i).hom =
      (second_step_iso j).hom ≫ T.system.map (opHomOfLE hij)

theorem represent_two_inverse_systems_by_bifiltered_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{max u v} C]
    [HasDerivedCategory.{w} C]
    {E : DerivedCategory C}
    (S T : DerivedInverseSystemWithMap E) :
    Nonempty (BiFilteredComplexRepresentsSystems S T) := by
  sorry

end Formalization.Books.Injectives.Unit13
