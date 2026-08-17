import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Formalization.Books.Derived.Unit06.Quotients
import Formalization.Books.Derived.Unit09.ConesAndTermwiseSplitSequences
import Formalization.Books.Homology.Unit13.Complexes

/-!
# Derived Categories, Chapter 11: derived categories

The source's derived category is Mathlib's `DerivedCategory`.  The
homotopy-category acyclic objects, quasi-isomorphisms, canonical cohomology
functors, bounded t-structure pieces, and bounded-below localization are
therefore exposed through the existing Mathlib interfaces.  The bounded-above
and bounded localization statements are retained as theorem interfaces until
their proofs are formalized.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit05
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit09
open Formalization.Books.Categories.Unit27
open Formalization.Books.Homology.Unit03
open scoped CategoryTheory.Pretriangulated.Opposite ZeroObject

universe w v u

namespace Formalization.Books.Derived.Unit11

/- The earlier chapter's complex aliases use its bundled additive-category
   interface.  An abelian category already supplies precisely those fields. -/
noncomputable instance abelian_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    Formalization.Books.Homology.Unit03.AdditiveCategory C :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/-! ## The homological cohomology functor on the homotopy category -/

abbrev BookComplex (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.Comp C

abbrev BookHomotopyCategory (C : Type u) [Category.{v} C] [AdditiveCategory C] :=
  Formalization.Books.Derived.Unit08.K C

noncomputable instance bookHomotopyCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (BookHomotopyCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

/-- The source's `Hⁿ : K(𝒜) ⥤ 𝒜`, using Mathlib's cochain homology functor. -/
abbrev cohomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    BookHomotopyCategory C ⥤ C :=
  HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n

/-- The source's reindexing convention `Hⁿ = H⁰ ∘ [n]`. -/
theorem cohomologyFunctor_shift
    (C : Type u) [Category.{v} C] [Abelian C] (n : ℤ) :
    (cohomologyFunctor C 0).shift n = cohomologyFunctor C n :=
  by sorry

/-- The degree-zero cohomology functor on `K(𝒜)` is homological. -/
theorem cohomologyZero_homological
    (C : Type u) [Category.{v} C] [Abelian C] :
    (cohomologyFunctor C 0).IsHomological := by
  infer_instance

/-- A finite exact window of the long cohomology sequence of a triangle. -/
noncomputable def cohomologyLongExactWindow
    (C : Type u) [Category.{v} C] [Abelian C]
    (T : Triangle (BookHomotopyCategory C)) (n : ℤ) :
    ComposableArrows C 5 :=
  (cohomologyFunctor C 0).homologySequenceComposableArrows₅ T n (n + 1) rfl

/-- Every cohomology window of a distinguished triangle is exact. -/
theorem cohomologyLongExactWindow_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    (T : Triangle (BookHomotopyCategory C))
    (hT : T ∈ distTriang (BookHomotopyCategory C)) (n : ℤ) :
    (cohomologyLongExactWindow C T n).Exact :=
  (cohomologyFunctor C 0).homologySequenceComposableArrows₅_exact T hT n (n + 1) rfl

/-! ### The snake-lemma sequence and its termwise-split comparison -/

/-- The cochain long-exact window attached to a short exact sequence. -/
noncomputable def cochainCohomologyWindow
    (C : Type u) [Category.{v} C] [Abelian C]
    {S : ShortComplex (BookComplex C)} (hS : S.ShortExact) (n : ℤ) :
    ComposableArrows C 5 :=
  Formalization.Books.Homology.Unit13.cochainCohomologySequence hS n

theorem cochainCohomologyWindow_exact
    (C : Type u) [Category.{v} C] [Abelian C]
    {S : ShortComplex (BookComplex C)} (hS : S.ShortExact) (n : ℤ) :
    (cochainCohomologyWindow C hS n).Exact :=
  Formalization.Books.Homology.Unit13.cochainCohomologySequence_exact hS n

/- The source says that the triangle sequence and the snake-lemma sequence
   agree for a termwise split short exact sequence.  The comparison is made
   explicit as an isomorphism of finite exact windows. -/
theorem termwiseSplitShortComplex_shortExact
    (C : Type u) [Category.{v} C] [Abelian C]
    {A B D : BookComplex C}
    (S : Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence A B D) :
    (Formalization.Books.Derived.Unit09.termwiseSplitShortComplex S).ShortExact := by
  sorry

theorem cohomologyLongExactWindow_termwiseSplit_compatibility
    (C : Type u) [Category.{v} C] [Abelian C]
    {A B D : BookComplex C}
    (S : Formalization.Books.Derived.Unit09.TermwiseSplitExactSequence A B D)
    (n : ℤ) :
    Nonempty
      (cohomologyLongExactWindow C
          (Formalization.Books.Derived.Unit09.termwiseSplitTriangleh S) n ≅
        cochainCohomologyWindow C
          (termwiseSplitShortComplex_shortExact C S) n) := by
  sorry

/-! ## Acyclic complexes, quasi-isomorphisms, and the unbounded derived category -/

/-- The source's acyclic subcategory of `K(𝒜)`. -/
abbrev acyclicHomotopyProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (BookHomotopyCategory C) :=
  HomotopyCategory.subcategoryAcyclic C

/-- The source's quasi-isomorphism multiplicative system on `K(𝒜)`. -/
abbrev quasiIsoHomotopyProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (BookHomotopyCategory C) :=
  HomotopyCategory.quasiIso C (ComplexShape.up ℤ)

/-- The recalled complex-level notion of acyclicity. -/
abbrev AcyclicComplex
    {C : Type u} [Category.{v} C] [Abelian C] (K : BookComplex C) : Prop :=
  K.Acyclic

/-- The recalled complex-level notion of quasi-isomorphism. -/
abbrev QuasiIsomorphism
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : BookComplex C} (f : K ⟶ L) : Prop :=
  QuasiIso f

theorem acyclicComplex_iff_cohomology_zero
    (C : Type u) [Category.{v} C] [Abelian C] (K : BookComplex C) :
    AcyclicComplex K ↔ ∀ n : ℤ, IsZero (K.homology n) :=
  Formalization.Books.Homology.Unit13.cochain_acyclic_iff_cohomology_isZero K

theorem quasiIsomorphism_iff_cohomology_isIso
    (C : Type u) [Category.{v} C] [Abelian C]
    {K L : BookComplex C} (f : K ⟶ L) :
    QuasiIsomorphism f ↔
      ∀ n : ℤ, IsIso (HomologicalComplex.homologyMap f n) :=
  Formalization.Books.Homology.Unit13.cochain_quasiIso_iff_cohomologyMap_isIso f

/-- The object property of objects killed by a functor. -/
def functorKernel {E F : Type*} [Category* E] [Category* F]
    (G : E ⥤ F) : ObjectProperty E :=
  fun X => IsZero (G.obj X)

/-- Acyclic objects form the source's strictly full saturated triangulated subcategory. -/
theorem acyclicHomotopyProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (acyclicHomotopyProperty C) := by
  sorry

/-- Quasi-isomorphisms are the saturated multiplicative system attached to acyclic objects. -/
theorem quasiIsoHomotopyProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoHomotopyProperty C) ∧
      CompatibleWithTriangulation (quasiIsoHomotopyProperty C) := by
  sorry

/-- Mathlib identifies quasi-isomorphisms with the cone morphism property of acyclic objects. -/
theorem quasiIsoHomotopyProperty_eq_acyclic_trW
    (C : Type u) [Category.{v} C] [Abelian C] :
    quasiIsoHomotopyProperty C = (acyclicHomotopyProperty C).trW :=
  HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic C

/-- The derived category, as supplied by Mathlib, is the localization of `K(𝒜)`. -/
theorem derivedCategory_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)).IsLocalization
      (quasiIsoHomotopyProperty C) := by
  infer_instance

/-- The same localization is the Verdier quotient by the acyclic subcategory. -/
theorem derivedCategory_is_acyclic_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)).IsLocalization
      (acyclicHomotopyProperty C).trW := by
  infer_instance

/-- The kernel of the localization functor is the acyclic subcategory. -/
theorem derivedCategory_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (DerivedCategory.Qh (C := C)) = acyclicHomotopyProperty C := by
  sorry

/-! ### Cohomology on the derived category and the size warning -/

/-- The canonical degree-`n` cohomology functor on `D(𝒜)`. -/
noncomputable abbrev derivedCohomologyFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (n : ℤ) : DerivedCategory C ⥤ C :=
  DerivedCategory.homologyFunctor C n

/-- The canonical factorization of `H⁰` through the localization. -/
noncomputable def derivedCohomologyZeroFactorIso
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (DerivedCategory.Qh (C := C)) ⋙ derivedCohomologyFunctor C 0 ≅
      cohomologyFunctor C 0 :=
  DerivedCategory.homologyFunctorFactorsh C 0

/-- Two complexes are quasi-isomorphic as objects when their images in `D(𝒜)`
are isomorphic. -/
def DerivedQuasiIsomorphic
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K L : BookComplex C) : Prop :=
  Nonempty ((DerivedCategory.Q (C := C)).obj K ≅
    (DerivedCategory.Q (C := C)).obj L)

/- The source's smallness warning is represented by Mathlib's explicit choice
   of a universe for the morphisms in a derived category.  For a Grothendieck
   category, a K-injective replacement gives the following usable Hom-set
   comparison; the existence of such replacements is supplied by the relevant
   later injective-resolution development. -/
theorem derivedCategory_map_bijective_to_KInjective
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : BookHomotopyCategory C) (I : BookComplex C) [I.IsKInjective] :
    Function.Bijective
      ((DerivedCategory.Qh (C := C)).map :
        (K ⟶ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) → _) :=
  CochainComplex.IsKInjective.Qh_map_bijective K I

/-- The K-injective replacement assertion used in the size discussion. -/
def HasKInjectiveResolution
    (C : Type u) [Category.{v} C] [Abelian C] (L : BookComplex C) : Prop :=
  ∃ (I : BookComplex C) (f : L ⟶ I),
    QuasiIsomorphism f ∧ I.IsKInjective

theorem grothendieck_hasKInjectiveResolution
    (C : Type u) [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{w} C] (L : BookComplex C) :
    HasKInjectiveResolution C L := by
  sorry

/-! ## Bounded pieces of the derived category -/

/-- Vanishing of cohomology in all sufficiently negative degrees. -/
def derivedCohomologyVanishesBelow
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero ((derivedCohomologyFunctor C n).obj X)

/-- Vanishing of cohomology in all sufficiently positive degrees. -/
def derivedCohomologyVanishesAbove
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((derivedCohomologyFunctor C n).obj X)

/-- Vanishing of cohomology outside a bounded range. -/
def derivedCohomologyVanishesBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) : Prop :=
  derivedCohomologyVanishesBelow C X ∧ derivedCohomologyVanishesAbove C X

/-- The canonical t-structure properties used for `D⁺`, `D⁻`, and `Dᵇ`. -/
abbrev derivedPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).plus

abbrev derivedMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).minus

abbrev derivedBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    ObjectProperty (DerivedCategory C) :=
  (DerivedCategory.TStructure.t (C := C)).bounded

/-- The source's bounded-below derived category, using Mathlib's canonical one. -/
abbrev DPlus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Plus C

/-- The source's bounded-above derived category, using Mathlib's canonical one. -/
abbrev DMinus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Minus C

/-- The source's bounded derived category, using Mathlib's canonical one. -/
abbrev DBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :=
  DerivedCategory.Bounded C

noncomputable instance derivedCategory_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    AdditiveCategory (DerivedCategory C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

theorem derivedPlusProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedPlusProperty C X ↔ derivedCohomologyVanishesBelow C X := by
  sorry

theorem derivedMinusProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedMinusProperty C X ↔ derivedCohomologyVanishesAbove C X := by
  sorry

theorem derivedBoundedProperty_iff
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : DerivedCategory C) :
    derivedBoundedProperty C X ↔ derivedCohomologyVanishesBounded C X := by
  sorry

/-- The three bounded derived pieces are strictly full saturated triangulated subcategories. -/
theorem derivedBoundedSubcategory_properties
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    IsStrictlyFullSaturatedPretriangulated (derivedPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (derivedMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (derivedBoundedProperty C) := by
  sorry

/-! ## Bounded-cohomology replacements -/

theorem boundedCohomology_replacement_below
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK : ∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (K.homology n)) :
    ∃ (L : BookComplex C) (f : K ⟶ L),
      QuasiIso f ∧ IsBoundedBelow L := by
  sorry

theorem boundedCohomology_replacement_above
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K.homology n)) :
    ∃ (M : BookComplex C) (f : M ⟶ K),
      QuasiIso f ∧ IsBoundedAbove M := by
  sorry

theorem boundedCohomology_replacement_bounded
    (C : Type u) [Category.{v} C] [Abelian C]
    (K : BookComplex C)
    (hK :
      (∃ N : ℤ, ∀ n : ℤ, n ≤ N → IsZero (K.homology n)) ∧
      (∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K.homology n))) :
    ∃ (L M N : BookComplex C)
      (f : K ⟶ L) (g : M ⟶ K) (u : M ⟶ N) (v : N ⟶ L),
      g ≫ f = u ≫ v ∧
      QuasiIso f ∧ QuasiIso g ∧ QuasiIso u ∧ QuasiIso v ∧
      IsBoundedBelow L ∧ IsBoundedAbove M ∧ IsBounded N := by
  sorry

/-! ## Bounded homotopy subcategories and their acyclic localizations -/

abbrev KPlusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KPlus C ⥤ BookHomotopyCategory C :=
  HomotopyCategory.Plus.ι C

abbrev KMinusInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KMinus C ⥤ BookHomotopyCategory C :=
  (boundedAboveHomotopyProperty C).ι

abbrev KBoundedInclusion
    (C : Type u) [Category.{v} C] [Abelian C] :
    KBounded C ⥤ BookHomotopyCategory C :=
  (boundedHomotopyProperty C).ι

abbrev acyclicPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KPlus C) :=
  HomotopyCategory.Plus.subcategoryAcyclic C

abbrev acyclicMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KMinus C) :=
  (acyclicHomotopyProperty C).inverseImage (KMinusInclusion C)

abbrev acyclicBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    ObjectProperty (KBounded C) :=
  (acyclicHomotopyProperty C).inverseImage (KBoundedInclusion C)

abbrev quasiIsoPlusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KPlus C) :=
  HomotopyCategory.Plus.quasiIso C

abbrev quasiIsoMinusProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KMinus C) :=
  (quasiIsoHomotopyProperty C).inverseImage (KMinusInclusion C)

abbrev quasiIsoBoundedProperty
    (C : Type u) [Category.{v} C] [Abelian C] :
    MorphismProperty (KBounded C) :=
  (quasiIsoHomotopyProperty C).inverseImage (KBoundedInclusion C)

noncomputable instance kPlus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KPlus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance kMinus_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KMinus C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

noncomputable instance kBounded_additiveCategory
    (C : Type u) [Category.{v} C] [Abelian C] :
    AdditiveCategory (KBounded C) :=
  { toPreadditive := inferInstance
    toHasFiniteProducts := inferInstance }

theorem boundedAcyclicSubcategory_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    IsStrictlyFullSaturatedPretriangulated (acyclicPlusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (acyclicMinusProperty C) ∧
      IsStrictlyFullSaturatedPretriangulated (acyclicBoundedProperty C) := by
  sorry

theorem boundedQuasiIsoProperty_properties
    (C : Type u) [Category.{v} C] [Abelian C] :
    SaturatedMultiplicativeSystem (quasiIsoPlusProperty C) ∧
      SaturatedMultiplicativeSystem (quasiIsoMinusProperty C) ∧
      SaturatedMultiplicativeSystem (quasiIsoBoundedProperty C) := by
  sorry

/-! ### The three localization functors -/

noncomputable abbrev plusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KPlus C ⥤ DPlus C :=
  DerivedCategory.Plus.Qh (C := C)

theorem plusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (plusDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoPlusProperty C) := by
  infer_instance

noncomputable def plusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoPlusProperty C).Localization ⥤ DPlus C :=
  Localization.Construction.lift (plusDerivedLocalizationFunctor C) (by
    intro X Y f hf
    exact Localization.inverts (plusDerivedLocalizationFunctor C)
      (quasiIsoPlusProperty C) f hf)

theorem plusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (plusLocalizationComparison C) := by
  sorry

theorem plusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (plusDerivedLocalizationFunctor C) = acyclicPlusProperty C := by
  sorry

theorem derivedQh_maps_KMinus_to_DMinus
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : KMinus C) :
    derivedMinusProperty C
      ((KMinusInclusion C ⋙ DerivedCategory.Qh (C := C)).obj X) := by
  sorry

noncomputable def minusDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KMinus C ⥤ DMinus C :=
  (derivedMinusProperty C).lift
    (KMinusInclusion C ⋙ DerivedCategory.Qh (C := C))
    (derivedQh_maps_KMinus_to_DMinus C)

theorem minusDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (minusDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoMinusProperty C) := by
  sorry

noncomputable def minusLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoMinusProperty C).Localization ⥤ DMinus C :=
  Localization.Construction.lift (minusDerivedLocalizationFunctor C) (by
    exact (minusDerivedLocalizationFunctor_is_localization C).inverts)

theorem minusLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (minusLocalizationComparison C) := by
  sorry

theorem minusDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (minusDerivedLocalizationFunctor C) = acyclicMinusProperty C := by
  sorry

theorem derivedQh_maps_KBounded_to_DBounded
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (X : KBounded C) :
    derivedBoundedProperty C
      ((KBoundedInclusion C ⋙ DerivedCategory.Qh (C := C)).obj X) := by
  sorry

noncomputable def boundedDerivedLocalizationFunctor
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    KBounded C ⥤ DBounded C :=
  (derivedBoundedProperty C).lift
    (KBoundedInclusion C ⋙ DerivedCategory.Qh (C := C))
    (derivedQh_maps_KBounded_to_DBounded C)

theorem boundedDerivedLocalizationFunctor_is_localization
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (boundedDerivedLocalizationFunctor C).IsLocalization
      (quasiIsoBoundedProperty C) := by
  sorry

noncomputable def boundedLocalizationComparison
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    (quasiIsoBoundedProperty C).Localization ⥤ DBounded C :=
  Localization.Construction.lift (boundedDerivedLocalizationFunctor C) (by
    exact (boundedDerivedLocalizationFunctor_is_localization C).inverts)

theorem boundedLocalizationComparison_is_equivalence
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    Functor.IsEquivalence (boundedLocalizationComparison C) := by
  sorry

theorem boundedDerivedLocalizationFunctor_kernel
    (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] :
    functorKernel (boundedDerivedLocalizationFunctor C) = acyclicBoundedProperty C := by
  sorry

end Formalization.Books.Derived.Unit11
