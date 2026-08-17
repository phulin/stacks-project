import Formalization.Books.Injectives.Unit02.BaersArgument
import Formalization.Books.Injectives.Unit10.GrothendieckConditions
import Formalization.Books.Sets.Unit07.Cofinality
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.ObjectProperty.Small
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Injectives, Chapter 11: Injectives in Grothendieck categories

This file records the definitions and theorem interfaces in the source section.
The canonical `Subobject`, `IsSeparator`, `Injective`, `IsAlphaSmall`, and
small-object APIs are used throughout; the proof stage supplies the proofs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w

namespace Formalization.Books.Injectives.Unit11

/-! ## Subobjects and size bounds -/

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cardinality of the hom-set from `U` to `X`, lifted to the universe of
the subobject type of `X`. -/
def homCardinal (U X : C) : Cardinal.{max u v} :=
  Cardinal.lift.{u} (Cardinal.mk (U ⟶ X))

/-- The cardinality of the type of subobjects of `X`. -/
def subobjectCardinal (X : C) : Cardinal.{max u v} :=
  Cardinal.mk (Subobject X)

/-- No strictly increasing subobject chain indexed by a cardinal larger than
the hom-cardinal of a generator exists. -/
theorem no_strictMono_subobject_chain
    (U X : C) (hU : IsSeparator U) (κ' : Cardinal.{max u v})
    (hκ : homCardinal U X < κ') :
    ¬ ∃ f : κ'.ord.ToType → Subobject X, StrictMono f := by
  sorry

/-- No strictly decreasing subobject chain indexed by a cardinal larger than
the hom-cardinal of a generator exists. -/
theorem no_strictAnti_subobject_chain
    (U X : C) (hU : IsSeparator U) (κ' : Cardinal.{max u v})
    (hκ : homCardinal U X < κ') :
    ¬ ∃ f : κ'.ord.ToType → Subobject X, StrictAnti f := by
  sorry

/-- An increasing ordinal-indexed subobject chain is eventually constant when
the ordinal has cofinality larger than the hom-cardinal of a generator. -/
theorem increasing_subobject_chain_eventually_constant
    (U X : C) (hU : IsSeparator U) (α : Ordinal.{max u v})
    (f : α.ToType → Subobject X) (hf : Monotone f)
    (hα : homCardinal U X < Ordinal.cof α) :
    ∃ β : α.ToType, ∀ γ : α.ToType, β ≤ γ → f γ = f β := by
  sorry

/-- A decreasing ordinal-indexed subobject chain is eventually constant when
the ordinal has cofinality larger than the hom-cardinal of a generator. -/
theorem decreasing_subobject_chain_eventually_constant
    (U X : C) (hU : IsSeparator U) (α : Ordinal.{max u v})
    (f : α.ToType → Subobject X) (hf : Antitone f)
    (hα : homCardinal U X < Ordinal.cof α) :
    ∃ β : α.ToType, ∀ γ : α.ToType, β ≤ γ → f γ = f β := by
  sorry

/-- The set of subobjects of `X` has cardinality at most the power set of the
hom-set from a generator to `X`. -/
theorem subobjectCardinal_le_power
    (U X : C) (hU : IsSeparator U) :
    subobjectCardinal X ≤ 2 ^ homCardinal U X := by
  sorry

/-! ## The size of an object -/

/-- The source's size of an object, expressed using Mathlib's canonical
subobject type. -/
def objectSize (M : C) : Cardinal.{max u v} := subobjectCardinal M

variable [IsGrothendieckAbelian.{max u v} C]

/-- In a Grothendieck abelian category every subobject type is small in the
universe used for `objectSize`. -/
theorem subobjects_are_small (M : C) : Small.{max u v} (Subobject M) := by
  infer_instance

/-- The size of either end of a short exact sequence is bounded by the size of
its middle term. -/
theorem objectSize_le_of_shortExact
    {M' M M'' : C} (f : M' ⟶ M) (g : M ⟶ M'') (hfg : f ≫ g = 0)
    (h : (ShortComplex.mk f g hfg).ShortExact) :
    objectSize M' ≤ objectSize M ∧ objectSize M'' ≤ objectSize M := by
  sorry

/-- The property of objects of size at most `κ`. -/
def objectsOfSizeAtMost (κ : Cardinal.{max u v}) : ObjectProperty C :=
  fun M => objectSize M ≤ κ

/-- Every object of size at most `κ` is a quotient of a coproduct of at most
`κ` copies of a generator. -/
theorem quotient_of_size_le
    (U : C) (hU : IsSeparator U) (M : C) (κ : Cardinal.{max u v})
    (hM : objectSize M ≤ κ) :
    ∃ (I : Type (max u v)) (_ : Cardinal.mk I ≤ κ)
      (f : (∐ fun _ : I => U) ⟶ M), Epi f := by
  sorry

/-- The isomorphism classes of objects of bounded size form a set. -/
theorem essentiallySmall_objectsOfSizeAtMost
    (κ : Cardinal.{max u v}) :
    ObjectProperty.EssentiallySmall.{max u v}
      (objectsOfSizeAtMost (C := C) κ) := by
  sorry

/-- An object is small with respect to injections at every ordinal whose
cofinality is larger than its size.  This reuses the chapter 2 definition of
`IsAlphaSmall`. -/
theorem object_is_alpha_small
    (M : C) (α : Ordinal.{max u v})
    (hα : objectSize M < Ordinal.cof α) :
    Formalization.Books.Injectives.Unit02.IsAlphaSmall M α
      (MorphismProperty.monomorphisms C) := by
  sorry

/-- Every cardinal has an ordinal with strictly larger cofinality. -/
theorem exists_ordinal_cofinality_gt (κ : Cardinal.{w}) :
    ∃ α : Ordinal.{w}, κ < Ordinal.cof α := by
  simpa using
    Formalization.Books.Sets.Unit07.exists_ordinal_cofinality_gt κ

/-! ## The generator-subobject criterion for injectivity -/

/-- To test injectivity, it suffices to test extensions from subobjects of a
generator. -/
theorem injective_iff_lifts_from_generator_subobjects
    (U I : C) (hU : IsSeparator U) :
    Injective I ↔
      ∀ (N : Subobject U) (f : (N : C) ⟶ I),
        ∃ g : U ⟶ I, N.arrow ≫ g = f := by
  sorry

/-! ## The functorial pushout and transfinite construction -/

/-- The arrow `M ⟶ 0`, used to turn the small-object construction into an
endofunctor on `C`. -/
def zeroArrowFunctor [HasZeroObject C] [HasZeroMorphisms C] : C ⥤ Arrow C where
  obj M := Arrow.mk (0 : M ⟶ 0)
  map f := Arrow.homMk f (𝟙 (0 : C)) (by simp)
  map_id := by
    intro M
    ext <;> simp
  map_comp := by
    intro M N P f g
    ext <;> simp

/-- One Grothendieck step, obtained by the canonical small-object pushout for
all subobject inclusions of the chosen generator. -/
noncomputable def grothendieckStepArrowFunctor (U : C) :
    Arrow C ⥤ Arrow C :=
  SmallObject.functor (fun N : Subobject U => N.arrow)

/-- The endofunctor `M ↦ 𝕄(M)` from the source's pushout construction. -/
noncomputable def grothendieckStepFunctor (U : C) : C ⥤ C :=
  zeroArrowFunctor ⋙ grothendieckStepArrowFunctor U ⋙ Arrow.leftFunc

/-- The object `𝕄(M)` in the source. -/
abbrev grothendieckStep (U M : C) : C :=
  (grothendieckStepFunctor U).obj M

/-- The functorial map `M ⟶ 𝕄(M)` supplied by the pushout construction. -/
noncomputable def grothendieckStepEmbedding (U : C) :
    𝟭 C ⟶ grothendieckStepFunctor U where
  app M :=
    (SmallObject.ε (fun N : Subobject U => N.arrow)).app
      ((zeroArrowFunctor (C := C)).obj M) |>.left
  naturality M N f := by
    change
      Arrow.leftFunc.map
          ((zeroArrowFunctor (C := C)).map f ≫
            (SmallObject.ε (fun N : Subobject U => N.arrow)).app
              ((zeroArrowFunctor (C := C)).obj N)) =
        Arrow.leftFunc.map
          ((SmallObject.ε (fun N : Subobject U => N.arrow)).app
              ((zeroArrowFunctor (C := C)).obj M) ≫
            (grothendieckStepArrowFunctor U).map
              ((zeroArrowFunctor (C := C)).map f))
    exact Arrow.leftFunc.congr_map
      ((SmallObject.ε (fun N : Subobject U => N.arrow)).naturality
        ((zeroArrowFunctor (C := C)).map f))

/-- Every map from a subobject of the generator extends across the first
pushout step. -/
theorem grothendieckStep_extension
    (U M : C) (N : Subobject U) (f : (N : C) ⟶ M) :
    ∃ g : U ⟶ grothendieckStep U M,
      N.arrow ≫ g = f ≫ (grothendieckStepEmbedding U).app M := by
  sorry

/-- The first-step map is monomorphic. -/
theorem grothendieckStepEmbedding_mono
    (U M : C) : Mono ((grothendieckStepEmbedding U).app M) := by
  sorry

/-- The successor structure for the source's transfinite iteration. -/
noncomputable def grothendieckSuccStruct (U : C) :
    CategoryTheory.SmallObject.SuccStruct (C ⥤ C) :=
  CategoryTheory.SmallObject.SuccStruct.ofNatTrans (grothendieckStepEmbedding U)

/-- The functor of stages below and including `α`. -/
noncomputable def grothendieckIterationFunctor (U : C) (α : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic α) (C ⥤ C)] :
    Set.Iic α ⥤ (C ⥤ C) :=
  (grothendieckSuccStruct U).iterationFunctor (Set.Iic α)

/-- The source's functor `M ↦ 𝕄_α(M)`. -/
noncomputable def grothendieckIteration (U : C) (α : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic α) (C ⥤ C)] : C ⥤ C :=
  (grothendieckIterationFunctor U α).obj ⟨α, by simp⟩

/-- The functorial map `M ⟶ 𝕄_α(M)`. -/
noncomputable def grothendieckIterationEmbedding (U : C) (α : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic α) (C ⥤ C)] :
    𝟭 C ⟶ grothendieckIteration U α :=
  ((grothendieckSuccStruct U).ιIterationFunctor (Set.Iic α)).app
    ⟨α, by simp⟩

/-- The diagram of earlier stages at a limit ordinal. -/
noncomputable def grothendieckIterationDiagram (U : C) (β : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic β) (C ⥤ C)] :
    Set.Iio β ⥤ (C ⥤ C) :=
  (Set.principalSegIioIicOfLE (le_rfl : β ≤ β)).monotone.functor ⋙
    grothendieckIterationFunctor U β

/-- The zero stage is the identity functor. -/
theorem grothendieckIteration_zero (U : C)
    [HasIterationOfShape (Set.Iic (0 : Ordinal.{max u v})) (C ⥤ C)] :
    Nonempty (grothendieckIteration U 0 ≅ 𝟭 C) := by
  sorry

/-- A successor stage is obtained by applying `𝕄`. -/
theorem grothendieckIteration_succ (U : C) (α : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic α) (C ⥤ C)]
    [HasIterationOfShape (Set.Iic (α + 1)) (C ⥤ C)] :
    Nonempty (grothendieckIteration U (α + 1) ≅
      grothendieckIteration U α ⋙ grothendieckStepFunctor U) := by
  sorry

/-- At a limit ordinal, the stage is the colimit of its earlier stages. -/
theorem grothendieckIteration_limit (U : C) (β : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic β) (C ⥤ C)]
    [HasColimit (grothendieckIterationDiagram U β)]
    (hβ : Order.IsSuccLimit β) :
    Nonempty (grothendieckIteration U β ≅
      colimit (grothendieckIterationDiagram U β)) := by
  sorry

/-- The transfinite construction gives an injective object and a monomorphic
functorial map once the cofinality of the iteration ordinal dominates the
generator's size. -/
theorem grothendieckIteration_injective
    (U : C) (hU : IsSeparator U) (M : C) (α : Ordinal.{max u v})
    [HasIterationOfShape (Set.Iic α) (C ⥤ C)]
    (hα : objectSize U < Ordinal.cof α) :
    Injective ((grothendieckIteration U α).obj M) ∧
      Mono ((grothendieckIterationEmbedding U α).app M) := by
  sorry

/-- Grothendieck abelian categories have functorial injective embeddings. -/
theorem has_functorial_injective_embeddings :
    ∃ (F : C ⥤ C) (η : 𝟭 C ⟶ F),
      (∀ M : C, Injective (F.obj M)) ∧
        (∀ M : C, Mono (η.app M)) := by
  sorry

end Formalization.Books.Injectives.Unit11
