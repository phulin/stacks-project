import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Formalization.Books.Derived.Unit07.AdjointsForExactFunctors
import Formalization.Books.Derived.Unit37.CompactObjects

/-!
# Derived Categories, Chapter 38: Brown representability

The source's compactly generated hypothesis is the canonical
`IsCompactlyGenerated` condition from Chapter 37.  Contravariant
cohomological functors are written as functors out of the opposite category,
and preservation of direct sums as products is expressed by Mathlib's
discrete-shape limit-preservation predicate.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open Formalization.Books.Derived.Unit06
open Formalization.Books.Derived.Unit07
open Formalization.Books.Derived.Unit36
open Formalization.Books.Derived.Unit33
open Formalization.Books.Derived.Unit37
open Formalization.Books.Homology.Unit03
open scoped BigOperators CategoryTheory.Pretriangulated.Opposite ZeroObject

universe v u v' u'

namespace Formalization.Books.Derived.Unit38

section BrownRepresentability

variable {D : Type u} [Category.{v} D] [AdditiveCategory D]
  [HasCoproducts.{v} D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [CategoryTheory.IsTriangulated D]

/-!
The proof chooses a compact generating family and then enlarges it, if
necessary, by shifts.  The following two interfaces keep that choice and the
shift-closure assertion available to the construction declarations below.
They do not replace `IsCompactlyGenerated`: the latter remains the canonical
chapter-37 hypothesis used by the main theorem.
-/
structure BrownCompactGenerator
    (D : Type u) [Category.{v} D] [AdditiveCategory D]
    [HasCoproducts.{v} D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [CategoryTheory.IsTriangulated D] where
  index : Type v
  object : index → D
  compact : ∀ i, IsCompactObject (object i)
  generator : IsGenerator (∐ object)

def BrownCompactGenerator.IsStableUnderShifts
    (P : BrownCompactGenerator (D := D)) : Prop :=
  ∀ (i : P.index) (n : ℤ),
    ∃ j : P.index, Nonempty (P.object j ≅ (P.object i)⟦n⟧)

/-! A chosen presentation extracted from the existential compact-generation
hypothesis.  This is a genuine choice of data, not a second compactness
definition. -/
noncomputable def brownCompactGeneratorPresentation
    (hD : IsCompactlyGenerated (C := D)) : BrownCompactGenerator (D := D) := by
  let I : Type v := Classical.choose hD
  let hI : ∃ E : I → D,
      (∀ i, IsCompactObject (E i)) ∧ IsGenerator (∐ E) :=
    Classical.choose_spec hD
  let E : I → D := Classical.choose hI
  let hE : (∀ i, IsCompactObject (E i)) ∧ IsGenerator (∐ E) :=
    Classical.choose_spec hI
  exact
    { index := I
      object := E
      compact := hE.1
      generator := hE.2 }

/-!
The shift-stable family used in the proof exists after replacing a compact
generating family by its shifts.  The source only uses this as a harmless
choice of generators, so the existence statement is the reusable interface.
-/
theorem exists_brown_shift_stable_compact_generator
    (hD : IsCompactlyGenerated (C := D)) :
    ∃ P : BrownCompactGenerator (D := D),
      P.IsStableUnderShifts := by
  sorry

/-!
The pairs `(Eᵢ, a)` in the first stage of the proof are represented by a
dependent sum.  The object and its coproduct map are canonical categorical
constructions; only the existence of the element with the required
components uses the product-preservation hypothesis.
-/
abbrev brownPairIndex
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  Σ i : P.index, (H.obj (Opposite.op (P.object i)) : Type v)

noncomputable def brownInitialObject
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) : D :=
  ∐ fun p : brownPairIndex P H => P.object p.1

theorem exists_brown_initial_element
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    ∃ a₁ : H.obj (Opposite.op (brownInitialObject P H)),
      ∀ p : brownPairIndex P H,
        H.map (Sigma.ι (fun p : brownPairIndex P H => P.object p.1) p).op a₁ = p.2 := by
  sorry

theorem exists_brown_initial_yoneda_map
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (a₁ : H.obj (Opposite.op (brownInitialObject P H))) :
    ∃ τ : preadditiveYoneda.obj (brownInitialObject P H) ⟶ H,
      (τ.app (Opposite.op (brownInitialObject P H))) (𝟙 _) = a₁ := by
  sorry

/-!
For a stage transformation `aₙ : Hom(-, Xₙ) ⟶ H`, this is the index of the
kernel elements used to form `Kₙ₊₁`.  The associated object and map use the
existing coproduct API, so they are available to later users independently of
the recursive existence theorem.
-/
abbrev brownKernelIndex
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (X : D)
    (a : preadditiveYoneda.obj X ⟶ H) :=
  Σ i : P.index,
    { k : (preadditiveYoneda.obj X).obj (Opposite.op (P.object i)) //
        (a.app (Opposite.op (P.object i))) k = 0 }

noncomputable def brownKernelObject
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (X : D)
    (a : preadditiveYoneda.obj X ⟶ H) : D :=
  ∐ fun q : brownKernelIndex P H X a => P.object q.1

noncomputable def brownKernelMap
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (X : D)
    (a : preadditiveYoneda.obj X ⟶ H) :
    brownKernelObject P H X a ⟶ X :=
  Sigma.desc (fun q : brownKernelIndex P H X a => q.2.1)

@[simp]
theorem brownKernelMap_ι
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) (X : D)
    (a : preadditiveYoneda.obj X ⟶ H)
    (q : brownKernelIndex P H X a) :
    Sigma.ι (fun q : brownKernelIndex P H X a => P.object q.1) q ≫
        brownKernelMap P H X a = q.2.1 := by
  unfold brownKernelMap
  exact Sigma.ι_desc _ _

/-!
The recursive part of the proof is recorded by a stage sequence.  The
transition kernel is the canonical `brownKernelObject`, and the fields expose
the initial surjectivity, the kernel-killing property, compatibility of the
Yoneda transformations, and the distinguished cone triangles used in the
induction.
-/
structure BrownStageSequence
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) where
  stages : SequentialSystem D
  transformations : ∀ n : ℕ,
    preadditiveYoneda.obj (stages.obj n) ⟶ H
  connecting : ∀ n : ℕ,
    stages.obj (n + 1) ⟶
      (brownKernelObject P H (stages.obj n) (transformations n))⟦(1 : ℤ)⟧
  startsWithInitialObject :
    Nonempty (stages.obj 0 ≅ brownInitialObject P H)
  initialGeneratorSurjective :
    ∀ i : P.index,
      Function.Surjective
        ((transformations 0).app (Opposite.op (P.object i)))
  compatible : ∀ n : ℕ,
    preadditiveYoneda.map (sequentialTransition stages n) ≫
        transformations (n + 1) = transformations n
  kernelKilled : ∀ (n : ℕ) (i : P.index)
    (f : P.object i ⟶ stages.obj n),
    (transformations n).app (Opposite.op (P.object i)) f = 0 →
      f ≫ sequentialTransition stages n = 0
  distinguished : ∀ n : ℕ,
    Triangle.mk
      (brownKernelMap P H (stages.obj n) (transformations n))
      (sequentialTransition stages n) (connecting n) ∈ distTriang D

theorem exists_brown_stage_sequence
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H) :
    Nonempty (BrownStageSequence P H) := by
  sorry

/-!
The source's `hocolim Xₙ` is Chapter 33's `IsDerivedColimit` presentation.
The chosen object and its defining triangle therefore reuse the existing
homotopy-colimit interface instead of introducing a parallel cone structure.
-/
theorem exists_brown_homotopy_colimit
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H) :
    ∃ K : D, IsDerivedColimit S.stages K := by
  exact exists_isDerivedColimit S.stages

noncomputable def brownHomotopyColimit
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H)
    (hS : ∃ K : D, IsDerivedColimit S.stages K) : D :=
  homotopyColimit S.stages hS

theorem brownHomotopyColimit_isDerivedColimit
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H)
    (hS : ∃ K : D, IsDerivedColimit S.stages K) :
    IsDerivedColimit S.stages (brownHomotopyColimit S hS) := by
  exact homotopyColimit_isDerivedColimit S.stages hS

/-! The two maps in the displayed product sequence obtained by applying `H`.
They are written with the source's right-to-left display as the forward maps
`H(K) ⟶ ∏ H(Xₙ) ⟶ ∏ H(Xₙ)`. -/
noncomputable abbrev brownStageProduct
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H) : AddCommGrpCat.{v} :=
  ∏ᶜ fun n : ℕ => H.obj (Opposite.op (S.stages.obj n))

noncomputable def brownProductComparison
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H) (K : D)
    (p : DerivedColimitPresentation S.stages K) :
    H.obj (Opposite.op K) ⟶ brownStageProduct S :=
  Pi.lift (fun n => H.map (p.ι n).op)

noncomputable def brownProductDifference
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H) :
    brownStageProduct S ⟶ brownStageProduct S :=
  Pi.lift (fun n =>
    Pi.π (fun n : ℕ => H.obj (Opposite.op (S.stages.obj n))) n -
      Pi.π (fun n : ℕ => H.obj (Opposite.op (S.stages.obj n))) (n + 1) ≫
        H.map (sequentialTransition S.stages n).op)

noncomputable def brownProductShortComplex
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H) (K : D)
    (p : DerivedColimitPresentation S.stages K)
    (hzero : brownProductComparison S K p ≫ brownProductDifference S = 0) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (brownProductComparison S K p) (brownProductDifference S) hzero

theorem brown_hocolim_product_exact
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H)
    [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {K : D} (p : DerivedColimitPresentation S.stages K) :
    ∃ hzero : brownProductComparison S K p ≫ brownProductDifference S = 0,
      (brownProductShortComplex S K p hzero).Exact := by
  sorry

/-! The element-lifting assertion used to choose the final natural
transformation.  The compatibility hypothesis is exactly the kernel
condition for the product difference map. -/
theorem exists_brown_hocolim_lift
    {P : BrownCompactGenerator (D := D)}
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}}
    (S : BrownStageSequence P H)
    [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {K : D} (p : DerivedColimitPresentation S.stages K)
    (a : ∀ n : ℕ, (H.obj (Opposite.op (S.stages.obj n)) : Type v))
    (ha : ∀ n : ℕ,
      H.map (sequentialTransition S.stages n).op (a (n + 1)) = a n) :
    ∃ aInf : H.obj (Opposite.op K),
      ∀ n : ℕ, H.map (p.ι n).op aInf = a n := by
  sorry

/-!
The map on a compact generator is the component of the final Yoneda
transformation.  The next interfaces record the source's surjectivity and
injectivity argument, while the canonical Chapter 33 comparison gives the
colimit-of-Hom identification used in that argument.
-/
noncomputable abbrev brownGeneratorComparison
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    {X : D} (τ : preadditiveYoneda.obj X ⟶ H) (i : P.index) :
    (preadditiveYoneda.obj X).obj (Opposite.op (P.object i)) ⟶
      H.obj (Opposite.op (P.object i)) :=
  τ.app (Opposite.op (P.object i))

theorem brown_compact_generator_hom_colimit_isIso
    (P : BrownCompactGenerator (D := D))
    (S : BrownStageSequence P H) {K : D}
    (p : DerivedColimitPresentation S.stages K) (i : P.index) :
    IsIso (compactHomColimitMap (D := D) (F := S.stages) (L := K)
      (K := P.object i) p) := by
  apply compact_hom_colimit_map_isIso p
  exact isCountablyCompact_of_isCompactObject _ (P.compact i)

theorem brown_generator_comparison_bijective
    (P : BrownCompactGenerator (D := D))
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (S : BrownStageSequence P H) {K : D}
    (p : DerivedColimitPresentation S.stages K)
    (τ : preadditiveYoneda.obj K ⟶ H)
    (hcompat : ∀ n : ℕ,
      preadditiveYoneda.map (p.ι n) ≫ τ = S.transformations n) :
    ∀ i : P.index, Function.Bijective (brownGeneratorComparison P H τ i) := by
  sorry

/-!
The final subcategory in the proof is an object property.  Its definition
keeps the source's “for every shift” clause explicit and uses the component
of the already constructed natural transformation.
-/
def brownRepresentabilitySubcategory
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    {X : D} (τ : preadditiveYoneda.obj X ⟶ H) : ObjectProperty D :=
  fun Y => ∀ n : ℤ, IsIso (τ.app (Opposite.op (Y⟦n⟧)))

theorem brownRepresentabilitySubcategory_is_strictlyFull_saturated_triangulated
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    {X : D} (τ : preadditiveYoneda.obj X ⟶ H) :
    (brownRepresentabilitySubcategory H τ).IsClosedUnderIsomorphisms ∧
      (brownRepresentabilitySubcategory H τ).IsTriangulated ∧
      IsSaturated (brownRepresentabilitySubcategory H τ) := by
  sorry

theorem brownRepresentabilitySubcategory_closed_under_coproducts
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {X : D} (τ : preadditiveYoneda.obj X ⟶ H) :
    ∀ (I : Type v) (Y : I → D),
      (∀ i, brownRepresentabilitySubcategory H τ (Y i)) →
        brownRepresentabilitySubcategory H τ (∐ Y) := by
  sorry

theorem brownRepresentabilitySubcategory_closed_under_derived_colimits
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    {X : D} (τ : preadditiveYoneda.obj X ⟶ H)
    {S : SequentialSystem D} {K : D}
    (p : DerivedColimitPresentation S K)
    (hS : ∀ n, brownRepresentabilitySubcategory H τ (S.obj n)) :
    brownRepresentabilitySubcategory H τ K := by
  sorry

theorem brownRepresentabilitySubcategory_contains_generators
    (P : BrownCompactGenerator (D := D))
    (hP : P.IsStableUnderShifts)
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (S : BrownStageSequence P H) {K : D}
    (p : DerivedColimitPresentation S.stages K)
    (τ : preadditiveYoneda.obj K ⟶ H)
    (hcompat : ∀ n : ℕ,
      preadditiveYoneda.map (p.ι n) ≫ τ = S.transformations n) :
    ∀ i : P.index, brownRepresentabilitySubcategory H τ (P.object i) := by
  sorry

theorem brownRepresentabilitySubcategory_eq_top
    (P : BrownCompactGenerator (D := D))
    (hP : P.IsStableUnderShifts)
    (H : Dᵒᵖ ⥤ AddCommGrpCat.{v}) [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    (S : BrownStageSequence P H) {K : D}
    (p : DerivedColimitPresentation S.stages K)
    (τ : preadditiveYoneda.obj K ⟶ H)
    (hcompat : ∀ n : ℕ,
      preadditiveYoneda.map (p.ι n) ≫ τ = S.transformations n) :
    brownRepresentabilitySubcategory H τ = (⊤ : ObjectProperty D) := by
  sorry

/-!
For the adjoint statement, the proof applies Brown representability to the
contravariant Hom functor `W ↦ Hom (F W) Y`.  This functor is represented
explicitly as a composite with the opposite of `F`; the two hypotheses needed
to apply Brown are recorded separately before the adjunction interface.
-/
noncomputable def brownAdjointTestFunctor
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    (F : D ⥤ D') (Y : D') : Dᵒᵖ ⥤ AddCommGrpCat.{v'} :=
  F.op ⋙ preadditiveYoneda.obj Y

theorem brownAdjointTestFunctor_isHomological
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (Y : D') :
    (brownAdjointTestFunctor F Y).IsHomological := by
  sorry

theorem brownAdjointTestFunctor_preserves_limits
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    (F : D ⥤ D') (hF : ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) F) (Y : D') :
    ∀ I : Type v,
      PreservesLimitsOfShape (Discrete I) (brownAdjointTestFunctor F Y) := by
  sorry

theorem exists_brown_representing_hom_equivalences
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') (hD : IsCompactlyGenerated (C := D))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F)
    (Y : D') :
    ∃ X : D, ∀ W : D, Nonempty ((W ⟶ X) ≃ (F.obj W ⟶ Y)) := by
  sorry

theorem exists_brown_right_adjoint
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') (hD : IsCompactlyGenerated (C := D))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F) :
    ∃ G : D' ⥤ D, Nonempty (F ⊣ G) := by
  sorry

/-!
The source proof is represented by the reusable interfaces above: the
pair-indexed first coproduct and Yoneda element, the recursive kernel objects
and distinguished triangles, the homotopy-colimit presentation and exact
product sequence, the compact-generator Hom comparison, and the final
strictly-full saturated triangulated subcategory argument.
-/

/-!
`H : Dᵒᵖ ⥤ Ab` is the source's contravariant cohomological functor.  The
source's condition that direct sums become products is the preservation of
all discrete limits indexed by the source's allowed small sets.
-/
theorem brown_representability
    (H : Dᵒᵖ ⥤ AddCommGrpCat)
    [H.IsHomological]
    (hH : ∀ I : Type v, PreservesLimitsOfShape (Discrete I) H)
    (hD : IsCompactlyGenerated (C := D)) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  sorry

/-!
An exact right adjoint packages the adjunction together with the canonical
shift-commutation data and the resulting triangulated-functor property.  This
is the source's phrase “exact right adjoint”, stated without choosing a
particular representative externally.
-/
def HasExactRightAdjoint
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') : Prop :=
  ∃ (G : D' ⥤ D) (_adj : F ⊣ G) (hG : G.CommShift ℤ),
    letI : G.CommShift ℤ := hG
    G.IsTriangulated

/-!
The Brown representability consequence: an exact functor preserving all
direct sums has an exact right adjoint.  Preservation is stated for the
source's full size of small coproduct diagrams.  The proof-level functor
`W ↦ Hom (F W) Y`, its Brown representing object, the resulting adjunction,
and the exactness of its right adjoint are accounted for by this interface;
the last step uses the canonical Chapter 7 adjoint-exactness result.
-/
theorem exact_right_adjoint_of_brown_representability
    {D' : Type u'} [Category.{v'} D'] [AdditiveCategory D']
    [HasShift D' ℤ] [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [Pretriangulated D'] [CategoryTheory.IsTriangulated D']
    (F : D ⥤ D') (hD : IsCompactlyGenerated (C := D))
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F) :
    HasExactRightAdjoint F := by
  sorry

end BrownRepresentability

end Formalization.Books.Derived.Unit38
