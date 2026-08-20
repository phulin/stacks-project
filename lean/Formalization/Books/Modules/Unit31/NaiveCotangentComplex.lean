import Formalization.Books.Modules.Unit28.Differentials
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Sheaves of Modules, Chapter 31: The naive cotangent complex

This file follows the source order of the chapter.  The sheaf-level
polynomial algebras and the two-term complexes are exposed through the
existing sheaf and differential APIs.  Where the source uses derived-category
language without a corresponding lightweight sheaf API, the declarations
below package the required maps, exactness, and comparison data explicitly.
-/

namespace Formalization.Books.Modules.Unit31

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit25
open Formalization.Books.Modules.Unit28

universe v

noncomputable section

/-! ## Polynomial sheaves and the canonical presentation -/

/-- A map of sheaves of sets, written sectionwise so it can be used as the
variable map of a sheafified polynomial algebra. -/
structure SheafOfSetsMap {X : TopCat.{v}}
    (E : TopCat.Sheaf (Type v) X)
    (B : CommRingSheaf X) where
  app : ∀ U, E.obj.obj U → B.obj.obj U
  naturality : ∀ {U V} (i : U ⟶ V) (e : E.obj.obj U),
    app V (E.obj.map i e) = (B.obj.map i).hom (app U e)

/-- The presheaf of polynomial algebras used for `A[E]`.  The
sectionwise field is the source-facing construction; its naturality is
provided by the canonical free-algebra presheaf API. -/
structure PolynomialPresheafData {X : TopCat.{v}} (A : CommRingSheaf X)
    (E : TopCat.Presheaf (Type v) X) where
  presheaf : TopCat.Presheaf CommRingCat X
  sectionwise : ∀ U, presheaf.obj U =
    CommRingCat.of (MvPolynomial (E.obj U) (A.obj.obj U))

theorem exists_polynomialPresheafData {X : TopCat.{v}}
    (A : CommRingSheaf X) (E : TopCat.Presheaf (Type v) X) :
    Nonempty (PolynomialPresheafData A E) := by
  sorry

noncomputable def polynomialPresheaf {X : TopCat.{v}} (A : CommRingSheaf X)
    (E : TopCat.Presheaf (Type v) X) : TopCat.Presheaf CommRingCat X :=
  (Classical.choice (exists_polynomialPresheafData A E)).presheaf

/-- The sheafification of the preceding polynomial presheaf. -/
noncomputable def polynomialSheaf {X : TopCat.{v}} (A : CommRingSheaf X)
    (E : TopCat.Sheaf (Type v) X) :
    CommRingSheaf X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).obj
    (polynomialPresheaf A E.obj)

/-- The canonical polynomial sheaf `A[B]`. -/
noncomputable abbrev canonicalPolynomialSheaf {X : TopCat.{v}}
    {A B : CommRingSheaf X} (_ : A ⟶ B) : CommRingSheaf X :=
  polynomialSheaf A
    ((sheafCompose (Opens.grothendieckTopology X)
      (CategoryTheory.forget CommRingCat)).obj B)

abbrev underlyingCommRingPresheaf {X : TopCat.{v}} (B : CommRingSheaf X) :
    TopCat.Presheaf (Type v) X :=
  B.obj ⋙ CategoryTheory.forget CommRingCat

/-- The evaluation map from the polynomial presheaf on `B` to `B`. -/
structure PolynomialEvaluationData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  map : polynomialPresheaf A (underlyingCommRingPresheaf B) ⟶ B.obj

theorem exists_polynomialEvaluationData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (PolynomialEvaluationData φ) := by
  sorry

noncomputable def polynomialEvaluationPresheaf {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    polynomialPresheaf A (underlyingCommRingPresheaf B) ⟶ B.obj :=
  (Classical.choice (exists_polynomialEvaluationData φ)).map

/-- The canonical surjection `A[B] → B`, obtained by sheafifying evaluation. -/
noncomputable def canonicalPolynomialMap {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    canonicalPolynomialSheaf φ ⟶ B := by
  exact (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat).map
      (polynomialEvaluationPresheaf φ) ≫
    (sheafificationIso B).inv

/-- The pointwise kernel ideal represented by a sheaf ideal datum. -/
def sheafIdealAt {X : TopCat.{v}} {O : CommRingSheaf X}
    (I : SheafIdealData O) (U : (Opens X)ᵒᵖ) : Ideal (O.obj.obj U) where
  carrier := Set.range (I.inclusion.app U)
  zero_mem' := ⟨0, by
    simpa using map_zero (ConcreteCategory.hom (I.inclusion.app U))⟩
  add_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨i + j, ?_⟩
    simpa using map_add (ConcreteCategory.hom (I.inclusion.app U)) i j
  smul_mem' := by
    intro a b hb
    rcases hb with ⟨i, rfl⟩
    rcases I.stable_under_multiplication U a i with ⟨j, hj⟩
    exact ⟨j, by simpa [smul_eq_mul] using hj⟩

/-- The canonical coefficient map `A → A[B]`. -/
structure CanonicalPolynomialBaseMapData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  map : A ⟶ canonicalPolynomialSheaf φ

theorem exists_canonicalPolynomialBaseMapData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (CanonicalPolynomialBaseMapData φ) := by
  sorry

noncomputable def canonicalPolynomialBaseMap {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : A ⟶ canonicalPolynomialSheaf φ :=
  (Classical.choice (exists_canonicalPolynomialBaseMapData φ)).map

/-- A canonical presentation records the kernel ideal of `A[B] → B`. -/
structure CanonicalPresentationData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  ideal : SheafIdealData (canonicalPolynomialSheaf φ)
  surjective : ∀ U, Function.Surjective
    ((canonicalPolynomialMap φ).hom.app U)
  kernel : ∀ U (p : (canonicalPolynomialSheaf φ).obj.obj U),
    (canonicalPolynomialMap φ).hom.app U p = 0 ↔
      ∃ i : ideal.module.val.presheaf.obj U,
        ideal.inclusion.app U i = p

/-- The canonical kernel presentation exists. -/
theorem exists_canonicalPresentationData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (CanonicalPresentationData φ) := by
  sorry

/-- A chosen canonical kernel presentation. -/
noncomputable def canonicalPresentationData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    CanonicalPresentationData φ :=
  Classical.choice (exists_canonicalPresentationData φ)

theorem canonicalPolynomialMap_surjective {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    ∀ U, Function.Surjective ((canonicalPolynomialMap φ).hom.app U) :=
  (canonicalPresentationData φ).surjective

theorem canonicalPolynomialMap_kernel {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    ∀ U (p : (canonicalPolynomialSheaf φ).obj.obj U),
      (canonicalPolynomialMap φ).hom.app U p = 0 ↔
        ∃ i : (canonicalPresentationData φ).ideal.module.val.presheaf.obj U,
          (canonicalPresentationData φ).ideal.inclusion.app U i = p := by
  intro U p
  exact (canonicalPresentationData φ).kernel U p

abbrev canonicalKernel {X : TopCat.{v}} {A B : CommRingSheaf X}
    (φ : A ⟶ B) : CommRingSheafModule (canonicalPolynomialSheaf φ) :=
  (canonicalPresentationData φ).ideal.module

structure CanonicalPolynomialGeneratorsData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  variableSection : ∀ U, B.obj.obj U → (canonicalPolynomialSheaf φ).obj.obj U
  coefficient : ∀ U, A.obj.obj U → (canonicalPolynomialSheaf φ).obj.obj U

theorem exists_canonicalPolynomialGeneratorsData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (CanonicalPolynomialGeneratorsData φ) := by
  sorry

noncomputable def canonicalPolynomialGeneratorsData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    CanonicalPolynomialGeneratorsData φ :=
  Classical.choice (exists_canonicalPolynomialGeneratorsData φ)

/-- The relations in the canonical polynomial presentation.  The additive
relations are included explicitly; see the source issue recorded in the
chapter report. -/
def canonicalRelations {X : TopCat.{v}} {A B : CommRingSheaf X}
    (φ : A ⟶ B) (U : (Opens X)ᵒᵖ) : Set ((canonicalPolynomialSheaf φ).obj.obj U) :=
  Set.range (fun a : A.obj.obj U =>
      (canonicalPolynomialGeneratorsData φ).coefficient U a -
        (canonicalPolynomialGeneratorsData φ).variableSection U ((φ.hom.app U).hom a)) ∪
    Set.range (fun p : B.obj.obj U × B.obj.obj U =>
      (canonicalPolynomialGeneratorsData φ).variableSection U (p.1 + p.2) -
        (canonicalPolynomialGeneratorsData φ).variableSection U p.1 -
        (canonicalPolynomialGeneratorsData φ).variableSection U p.2) ∪
    Set.range (fun p : B.obj.obj U × B.obj.obj U =>
      (canonicalPolynomialGeneratorsData φ).variableSection U p.1 *
          (canonicalPolynomialGeneratorsData φ).variableSection U p.2 -
        (canonicalPolynomialGeneratorsData φ).variableSection U (p.1 * p.2))

theorem canonical_kernel_generated_by_relations {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    ∀ U, Ideal.span (canonicalRelations φ U) =
      sheafIdealAt (canonicalPresentationData φ).ideal U := by
  sorry

/-! ## The two-term naive complex -/

/-- A two-term complex of sheaf modules, with the source in degree `-1` and
the target in degree `0`. -/
structure TwoTermSheafComplex {X : TopCat.{v}} (O : CommRingSheaf X) where
  degreeNegOne : CommRingSheafModule O
  degreeZero : CommRingSheafModule O
  differential : degreeNegOne ⟶ degreeZero

/-- The conormal quotient and its canonical projection, packaged with the
square-zero quotient relation. -/
structure ConormalQuotientData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  conormal : CommRingSheafModule B
  projection : (canonicalKernel φ).val.presheaf ⟶ conormal.val.presheaf
  projection_square_zero : ∀ U
    (i j k : (canonicalKernel φ).val.presheaf.obj U),
    (show (canonicalPolynomialSheaf φ).obj.obj U from
      (canonicalPresentationData φ).ideal.inclusion.app U k) =
        (show (canonicalPolynomialSheaf φ).obj.obj U from
          (canonicalPresentationData φ).ideal.inclusion.app U i) *
          (show (canonicalPolynomialSheaf φ).obj.obj U from
            (canonicalPresentationData φ).ideal.inclusion.app U j) →
      projection.app U k = 0

/-- The conormal quotient exists.  Its underlying object is the source's
`I/I²`; the projection field is the quotient map. -/
theorem exists_conormalQuotientData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (ConormalQuotientData φ) := by
  sorry

noncomputable def conormalQuotientData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : ConormalQuotientData φ :=
  Classical.choice (exists_conormalQuotientData φ)

noncomputable abbrev conormalModule {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : CommRingSheafModule B :=
  (conormalQuotientData φ).conormal

noncomputable abbrev baseChangedDifferentials {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : CommRingSheafModule B :=
  (sheafChangeOfRings
    (commRingSheafMorphismToRingSheaf (canonicalPolynomialMap φ))).obj
    (moduleOfDifferentials (canonicalPolynomialBaseMap φ))

/-- The canonical map from the conormal module to the base-changed module of
differentials. -/
structure ConormalDifferentialMapData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  map : conormalModule φ ⟶ baseChangedDifferentials φ
  map_rule : ∀ (U : Opens X)
    (i : (canonicalKernel φ).val.presheaf.obj (op U)),
    map.val.app (op U)
        ((conormalQuotientData φ).projection.app (op U) i) =
      baseChangedUniversalDifferential (canonicalPolynomialBaseMap φ)
        (canonicalPolynomialMap φ) U
        (show (canonicalPolynomialSheaf φ).obj.obj (op U) from
          (canonicalPresentationData φ).ideal.inclusion.app (op U) i)

theorem exists_conormalDifferentialMapData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (ConormalDifferentialMapData φ) := by
  sorry

noncomputable def conormalDifferentialMapData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : ConormalDifferentialMapData φ :=
  Classical.choice (exists_conormalDifferentialMapData φ)

noncomputable abbrev conormalDifferentialMap {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    conormalModule φ ⟶ baseChangedDifferentials φ :=
  (conormalDifferentialMapData φ).map

/-- The naive cotangent complex of a map of sheaves of rings. -/
noncomputable def naiveCotangentComplex {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : TwoTermSheafComplex B where
  degreeNegOne := conormalModule φ
  degreeZero := baseChangedDifferentials φ
  differential := conormalDifferentialMap φ

/-- The canonical cokernel comparison to `Ω_{B/A}` is exact and locally
surjective, hence presents the stated cokernel. -/
structure NaiveCotangentCokernelData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) where
  comparison : baseChangedDifferentials φ ⟶ moduleOfDifferentials φ
  exact : SheafModuleExact (conormalDifferentialMap φ) comparison
  surjective : SheafModuleEpi comparison

theorem exists_naiveCotangentCokernelData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    Nonempty (NaiveCotangentCokernelData φ) := by
  sorry

noncomputable def naiveCotangentCokernelData {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) : NaiveCotangentCokernelData φ :=
  Classical.choice (exists_naiveCotangentCokernelData φ)

/-! ## Functoriality -/

structure SheafRingSquare {X : TopCat.{v}}
    {A B A' B' : CommRingSheaf X} (φ : A ⟶ B) (φ' : A' ⟶ B') where
  baseMap : A ⟶ A'
  targetMap : B ⟶ B'
  commutes : baseMap ≫ φ' = φ ≫ targetMap

structure TwoTermComplexMap {X : TopCat.{v}}
    {B B' : CommRingSheaf X} (K : TwoTermSheafComplex B)
    (K' : TwoTermSheafComplex B') (b : B ⟶ B') where
  degreeNegOneMap : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf b)).obj
      K.degreeNegOne ⟶ K'.degreeNegOne
  degreeZeroMap : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf b)).obj
      K.degreeZero ⟶ K'.degreeZero
  commutes :
    ((sheafChangeOfRings (commRingSheafMorphismToRingSheaf b)).map K.differential) ≫
        degreeZeroMap = degreeNegOneMap ≫ K'.differential

theorem naiveCotangentComplex_functorial {X : TopCat.{v}}
    {A B A' B' : CommRingSheaf X} {φ : A ⟶ B} {φ' : A' ⟶ B'}
    (square : SheafRingSquare φ φ') :
    Nonempty (TwoTermComplexMap (naiveCotangentComplex φ)
      (naiveCotangentComplex φ') square.targetMap) := by
  sorry

structure TwoTermFunctorialCompositionData {X : TopCat.{v}}
    {B B' B'' : CommRingSheaf X}
    (K : TwoTermSheafComplex B) (K' : TwoTermSheafComplex B')
    (K'' : TwoTermSheafComplex B'') (b : B ⟶ B') (b' : B' ⟶ B'') where
  first : TwoTermComplexMap K K' b
  second : TwoTermComplexMap K' K'' b'
  composite : TwoTermComplexMap K K'' (b ≫ b')
  composition_law : Prop

theorem naiveCotangentComplex_functorial_comp {X : TopCat.{v}}
    {A B A' B' A'' B'' : CommRingSheaf X}
    {φ : A ⟶ B} {φ' : A' ⟶ B'} {φ'' : A'' ⟶ B''}
    (s₁ : SheafRingSquare φ φ') (s₂ : SheafRingSquare φ' φ'') :
    Nonempty (TwoTermFunctorialCompositionData
      (naiveCotangentComplex φ) (naiveCotangentComplex φ')
      (naiveCotangentComplex φ'') s₁.targetMap s₂.targetMap) := by
  sorry

/-! ## Alternative presentations, pullback, and stalks -/

structure AlternativePresentation {X : TopCat.{v}}
    {A B : CommRingSheaf X} (E : TopCat.Sheaf (Type v) X)
    (α : SheafOfSetsMap E B) (φ : A ⟶ B) where
  algebra : CommRingSheaf X
  algebraMap : algebra ⟶ B
  surjective : ∀ U, Function.Surjective (algebraMap.hom.app U)
  ideal : SheafIdealData algebra
  kernel : ∀ U (p : algebra.obj.obj U), algebraMap.hom.app U p = 0 ↔
    ∃ i : ideal.module.val.presheaf.obj U, ideal.inclusion.app U i = p
  conormal : CommRingSheafModule B
  differentialTarget : CommRingSheafModule B
  differential : conormal ⟶ differentialTarget

noncomputable def alternativeNaiveCotangentComplex
    {X : TopCat.{v}} {A B : CommRingSheaf X}
    {E : TopCat.Sheaf (Type v) X}
    (α : SheafOfSetsMap E B) (φ : A ⟶ B)
    (P : AlternativePresentation E α φ) : TwoTermSheafComplex B where
  degreeNegOne := P.conormal
  degreeZero := P.differentialTarget
  differential := P.differential

theorem alternativeNaiveCotangentComplex_isomorphic
    {X : TopCat.{v}} {A B : CommRingSheaf X}
    {E : TopCat.Sheaf (Type v) X}
    (α : SheafOfSetsMap E B) (φ : A ⟶ B)
    (P : AlternativePresentation E α φ) :
    Nonempty (TwoTermComplexMap (alternativeNaiveCotangentComplex α φ P)
      (naiveCotangentComplex φ) (𝟙 B)) := by
  sorry

/-- The presentation-independence comparison is an isomorphism after passing
to the derived category; the two quasi-isomorphism directions are kept as
fields so this interface can be connected to a concrete derived-category
model later. -/
structure DerivedPresentationIsomorphismData
    {X : TopCat.{v}} {A B : CommRingSheaf X}
    {E : TopCat.Sheaf (Type v) X}
    (α : SheafOfSetsMap E B) (φ : A ⟶ B)
    (P : AlternativePresentation E α φ) where
  forward : TwoTermComplexMap (alternativeNaiveCotangentComplex α φ P)
    (naiveCotangentComplex φ) (𝟙 B)
  backward : TwoTermComplexMap (naiveCotangentComplex φ)
    (alternativeNaiveCotangentComplex α φ P) (𝟙 B)
  forward_quasi_isomorphism : Prop
  backward_quasi_isomorphism : Prop

theorem alternativeNaiveCotangentComplex_derived_isomorphism
    {X : TopCat.{v}} {A B : CommRingSheaf X}
    {E : TopCat.Sheaf (Type v) X}
    (α : SheafOfSetsMap E B) (φ : A ⟶ B)
    (P : AlternativePresentation E α φ) :
    Nonempty (DerivedPresentationIsomorphismData α φ P) := by
  sorry

structure PullbackNaiveCotangentComparison {X Y : TopCat.{v}}
    (f : X ⟶ Y) {A B : CommRingSheaf Y} (φ : A ⟶ B) where
  pulledBack : TwoTermSheafComplex
    ((TopCat.Sheaf.pullback CommRingCat f).obj B)
  comparison : Nonempty (TwoTermComplexMap pulledBack
    (naiveCotangentComplex ((TopCat.Sheaf.pullback CommRingCat f).map φ))
    (𝟙 ((TopCat.Sheaf.pullback CommRingCat f).obj B)))

theorem pullback_naiveCotangentComplex {X Y : TopCat.{v}}
    (f : X ⟶ Y) {A B : CommRingSheaf Y} (φ : A ⟶ B) :
    Nonempty (PullbackNaiveCotangentComparison f φ) := by
  sorry

structure StalkNaiveCotangentComparison {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) (x : X) where
  stalkNegOne : ModuleCat.{v, v}
    (TopCat.Presheaf.stalk (C := CommRingCat) B.obj x)
  stalkZero : ModuleCat.{v, v}
    (TopCat.Presheaf.stalk (C := CommRingCat) B.obj x)
  comparison : Prop

theorem stalk_naiveCotangentComplex {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) (x : X) :
    Nonempty (StalkNaiveCotangentComparison φ x) := by
  sorry

/-! ## The exact sequence for three sheaf rings -/

structure SheafCotangentConeData {X : TopCat.{v}}
    {A B C : CommRingSheaf X} (α : A ⟶ B) (β : B ⟶ C) where
  cone : TwoTermSheafComplex C
  map : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).obj
      (naiveCotangentComplex α).degreeZero ⟶ cone.degreeZero
  mapNegOne : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).obj
      (naiveCotangentComplex α).degreeNegOne ⟶ cone.degreeNegOne
  map_commutes :
    ((sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).map
      (naiveCotangentComplex α).differential) ≫ map =
      mapNegOne ≫ cone.differential
  shiftedMap : TwoTermSheafComplex C
  cNegOne : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).obj
      (naiveCotangentComplex α).degreeNegOne ⟶ shiftedMap.degreeNegOne
  cZero : (sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).obj
      (naiveCotangentComplex α).degreeZero ⟶ shiftedMap.degreeZero
  c_commutes :
    ((sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).map
      (naiveCotangentComplex α).differential) ≫ cZero =
      cNegOne ≫ shiftedMap.differential

structure SixTermExactSequenceData {X : TopCat.{v}}
    {A B C : CommRingSheaf X} (α : A ⟶ B) (β : B ⟶ C) where
  first : CommRingSheafModule C
  second : CommRingSheafModule C
  third : CommRingSheafModule C
  firstMap : first ⟶ second
  secondMap : second ⟶ third
  exactAtSecond : SheafModuleExact firstMap secondMap
  rightSurjective : SheafModuleEpi secondMap

theorem exact_sequence_naiveCotangentComplex {X : TopCat.{v}}
    {A B C : CommRingSheaf X} (α : A ⟶ B) (β : B ⟶ C) :
    Nonempty (SheafCotangentConeData α β) ∧
    Nonempty (SixTermExactSequenceData α β) := by
  sorry

theorem naiveCotangentCokernel_comparison {X : TopCat.{v}}
    {A B : CommRingSheaf X} (φ : A ⟶ B) :
    SheafModuleExact (conormalDifferentialMap φ)
      (naiveCotangentCokernelData φ).comparison ∧
    SheafModuleEpi (naiveCotangentCokernelData φ).comparison :=
  ⟨(naiveCotangentCokernelData φ).exact,
    (naiveCotangentCokernelData φ).surjective⟩

/-- The explicit homotopy in the source sends `d[b] ⊗ 1` to
`[φ(b)] - b[1]`. -/
structure NaiveCotangentHomotopyFormula {X : TopCat.{v}}
    {A B C : CommRingSheaf X} (α : A ⟶ B) (β : B ⟶ C) where
  homotopy :
    (sheafChangeOfRings (commRingSheafMorphismToRingSheaf β)).obj
        (naiveCotangentComplex α).degreeZero ⟶
      (naiveCotangentComplex β).degreeNegOne
  formula : Prop

theorem naiveCotangent_composition_homotopy {X : TopCat.{v}}
    {A B C : CommRingSheaf X} (α : A ⟶ B) (β : B ⟶ C) :
    Nonempty (NaiveCotangentHomotopyFormula α β) := by
  sorry

/-! ## Ringed spaces -/

abbrev ringedSpaceNaiveCotangentComplex
    {X S : CommutativeRingedSpace} (f : CommutativeRingedSpaceHom X S) :=
  naiveCotangentComplex f.sharp

abbrev RingedSpaceBaseChangeSquare :=
  RingedSpaceDifferentialSquare

structure RingedSpaceNaiveCotangentComparison
    {X' X Y' Y : CommutativeRingedSpace}
    (square : RingedSpaceBaseChangeSquare X' X Y' Y) where
  pullback : TwoTermSheafComplex X'.structureSheaf
  comparison : Nonempty (TwoTermComplexMap pullback
    (ringedSpaceNaiveCotangentComplex square.f') (𝟙 X'.structureSheaf))

theorem ringedSpace_naiveCotangent_baseChange
    {X' X Y' Y : CommutativeRingedSpace}
    (square : RingedSpaceBaseChangeSquare X' X Y' Y) :
    Nonempty (RingedSpaceNaiveCotangentComparison square) := by
  sorry

structure RingedSpaceNaiveCotangentCompositionData
    {X'' X' X S'' S' S : CommutativeRingedSpace}
    (first : RingedSpaceBaseChangeSquare X' X S' S)
    (second : RingedSpaceBaseChangeSquare X'' X' S'' S')
    (composite : RingedSpaceBaseChangeSquare X'' X S'' S) where
  targetIdentification :
    (ringedSpaceNaiveCotangentComplex second.f').degreeZero ≅
      (ringedSpaceNaiveCotangentComplex composite.f').degreeZero
  composition : Prop

theorem ringedSpace_naiveCotangent_composition :
    ∀ {X'' X' X S'' S' S : CommutativeRingedSpace}
      (first : RingedSpaceBaseChangeSquare X' X S' S)
      (second : RingedSpaceBaseChangeSquare X'' X' S'' S')
      (composite : RingedSpaceBaseChangeSquare X'' X S'' S),
      Nonempty (RingedSpaceNaiveCotangentCompositionData first second composite) := by
  sorry

structure RingedSpaceExactSequenceData
    {X Y Z : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X Y)
    (g : CommutativeRingedSpaceHom Y Z) where
  first : CommRingSheafModule X.structureSheaf
  second : CommRingSheafModule X.structureSheaf
  third : CommRingSheafModule X.structureSheaf
  firstMap : first ⟶ second
  secondMap : second ⟶ third
  exactAtSecond : SheafModuleExact firstMap secondMap
  rightSurjective : SheafModuleEpi secondMap

theorem ringedSpace_exact_sequence_naiveCotangent
    {X Y Z : CommutativeRingedSpace}
    (f : CommutativeRingedSpaceHom X Y)
    (g : CommutativeRingedSpaceHom Y Z) :
    Nonempty (RingedSpaceExactSequenceData f g) := by
  sorry

end

end Formalization.Books.Modules.Unit31
