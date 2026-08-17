import Formalization.Books.MoreAlgebra.Unit55.InjectiveModules
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.SmallObject.Construction
import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Injectives, Chapter 2: Baer's argument for modules

This file formalizes the definitions and theorem interfaces in the chapter.
The comparison map uses the covariant representable functor `Hom(A, -)`, and
the large pushout is implemented by Mathlib's canonical small-object
construction for the family of ideal inclusions.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Formalization.Books.Injectives.Unit02

/-! ## The comparison map and its set-theoretic examples -/

/-- The comparison map from the colimit of the hom-sets to the hom-set of the
colimit.  This is equation (compare) in the source. -/
noncomputable def comparisonMap
    {C : Type u} [Category.{v} C]
    {J : Type w} [Category.{w} J]
    (A : C) (F : J ⥤ C) [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :
    colimit (F ⋙ coyoneda.obj (Opposite.op A)) →
      (A ⟶ colimit F) :=
  colimit.desc (F ⋙ coyoneda.obj (Opposite.op A))
    { pt := A ⟶ colimit F
      ι :=
        { app := fun j =>
            (coyoneda.obj (Opposite.op A)).map (colimit.ι F j)
          naturality := by
            intro j k f
            ext g
            change (g ≫ F.map f) ≫ colimit.ι F k = g ≫ colimit.ι F j
            rw [Category.assoc, colimit.w] } }

/-- The ordinal-indexed form of the comparison map. -/
abbrev ordinalComparisonMap
    {C : Type u} [Category.{v} C]
    (A : C) (α : Ordinal.{w}) (F : Set.Iio α ⥤ C)
    [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :=
  comparisonMap A F

/-- The finite-source assertion is a bijectivity statement for the comparison
map, with the existence of the two colimits made explicit. -/
def comparisonMapBijective
    {C : Type u} [Category.{v} C]
    {J : Type w} [Category.{w} J]
    (A : C) (F : J ⥤ C) (hF : HasColimit F)
    (hHom : HasColimit (F ⋙ coyoneda.obj (Opposite.op A))) : Prop :=
  letI := hF
  letI := hHom
  Function.Bijective (comparisonMap A F)

/-- A finite set is small for every ordinal-indexed system of sets. -/
theorem comparisonMap_bijective_of_finite
    (α : Ordinal.{w}) (A : Type u) [Finite A]
    (F : Set.Iio α ⥤ Type u) [HasColimit F]
    [HasColimit (F ⋙ coyoneda.obj (Opposite.op A))] :
    Function.Bijective (comparisonMap A F) := by
  sorry

/-- The increasing finite-set diagram used in the first counterexample.  We
use `Fin (n + 1)` as the zero-based version of `{1, ..., n}`. -/
def finiteSetChain : ℕ ⥤ Type where
  obj n := Fin (n + 1)
  map {n m} h :=
    ↾(fun x : Fin (n + 1) =>
      ⟨x.1, Nat.lt_of_lt_of_le x.2
        (Nat.succ_le_succ (leOfHom h))⟩)
  map_id := by
    intro n
    ext x
    rfl
  map_comp := by
    intro n m k h₁ h₂
    ext x
    rfl

/-- The map from `ℕ` to the colimit of the finite-set chain which sends `n` to
the image of the largest element of the `n`th stage. -/
noncomputable def finiteSetChainColimitMap :
    ℕ → colimit finiteSetChain :=
  fun n => colimit.ι finiteSetChain n ⟨n, Nat.lt_succ_self n⟩

/-- The map in the first example does not factor through any finite stage. -/
theorem finiteSetChain_no_finite_factor :
    ∀ n : ℕ, ¬ ∃ g : ℕ → finiteSetChain.obj n,
      ∀ k : ℕ,
        colimit.ι finiteSetChain n (g k) =
          finiteSetChainColimitMap k := by
  sorry

/-- Consequently the comparison map in the first example is not surjective. -/
theorem finiteSetChain_comparison_not_surjective :
    ¬ Function.Surjective
      (comparisonMap (A := ℕ) finiteSetChain) := by
  sorry

/-- The setoid which collapses the initial segment `{0, ..., n - 1}` of `ℕ`
to one point. -/
def collapsedSetoid (n : ℕ) : Setoid ℕ where
  r a b := a = b ∨ (a < n ∧ b < n)
  iseqv :=
    { refl := by
        intro a
        exact Or.inl rfl
      symm := by
        intro a b h
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨h.2, h.1⟩
      trans := by
        intro a b c hab hbc
        rcases hab with hab | hab
        · subst hab
          exact hbc
        · rcases hbc with hbc | hbc
          · subst hbc
            exact Or.inr hab
          · exact Or.inr ⟨hab.1, hbc.2⟩ }

abbrev collapsedQuotient (n : ℕ) := Quotient (collapsedSetoid n)

/-- The transition map between the collapsed quotients. -/
def collapsedMap {n m : ℕ} (h : n ≤ m) :
    collapsedQuotient n → collapsedQuotient m :=
  Quotient.map id (by
    intro a b hab
    rcases hab with hab | hab
    · exact Or.inl hab
    · exact Or.inr ⟨Nat.lt_of_lt_of_le hab.1 h, Nat.lt_of_lt_of_le hab.2 h⟩)

/-- The increasing system of quotients used in the second counterexample. -/
def collapsedNatChain : ℕ ⥤ Type where
  obj n := collapsedQuotient n
  map {n m} h := ↾(collapsedMap (leOfHom h))
  map_id := by
    intro n
    ext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl
  map_comp := by
    intro n m k h₁ h₂
    ext x
    refine Quotient.inductionOn x ?_
    intro a
    rfl

/-- The natural projection `ℕ → Bₙ` in the second example. -/
def collapsedProjection (n : ℕ) : ℕ → collapsedQuotient n :=
  @Quotient.mk' ℕ (collapsedSetoid n)

/-- The constant map to the class of `0` in `Bₙ`. -/
def collapsedConstant (n : ℕ) : ℕ → collapsedQuotient n :=
  fun _ => @Quotient.mk' ℕ (collapsedSetoid n) 0

/-- The colimit of the collapsed-quotient chain is a one-point set. -/
theorem collapsedNatChain_colimit_subsingleton :
    Subsingleton (colimit collapsedNatChain) := by
  sorry

/-- The two displayed families of maps in the second example are distinct at
each finite stage. -/
theorem collapsedProjection_ne_collapsedConstant (n : ℕ) :
    collapsedProjection n ≠ collapsedConstant n := by
  sorry

/-- The comparison map in the second example is not injective. -/
theorem collapsedNatChain_comparison_not_injective :
    ¬ Function.Injective
      (comparisonMap (A := ℕ) collapsedNatChain) := by
  sorry

/-! ## Small objects and module colimits -/

/-- An object is `α`-small with respect to a morphism property when every
ordinal-indexed diagram whose transition maps satisfy that property has a
bijective comparison map. -/
def IsAlphaSmall
    {C : Type u} [Category.{v} C] (A : C) (α : Ordinal.{w})
    (P : MorphismProperty C) : Prop :=
  ∀ (F : Set.Iio α ⥤ C),
    (∀ {i j : Set.Iio α} (f : i ⟶ j), P (F.map f)) →
    ∀ (hF : HasColimit F)
      (hHom : HasColimit (F ⋙ coyoneda.obj (Opposite.op A))),
      comparisonMapBijective A F hF hHom

/-- For an ordinal chain of modules with monomorphic transition maps, every
stage maps monomorphically into the colimit. -/
theorem ordinal_module_colimit_ι_mono
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    ∀ i : Set.Iio α, Mono (colimit.ι F i) := by
  sorry

/-- With monomorphic transition maps, the comparison map out of any module
 is injective. -/
theorem module_comparisonMap_injective
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (A : ModuleCat.{u} R) (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    Function.Injective (comparisonMap A F) := by
  sorry

/-- In the concrete module interpretation of the ordinal colimit, the
underlying module is the union of the images of its stages. -/
theorem ordinal_module_colimit_union
    {R : Type u} [Ring R] {α : Ordinal.{u}}
    (F : Set.Iio α ⥤ ModuleCat.{u} R)
    (hα : 0 < α)
    (hF : ∀ {i j : Set.Iio α} (f : i ⟶ j), Mono (F.map f)) :
    (Set.univ : Set (↑(colimit F : ModuleCat.{u} R))) =
      ⋃ i : Set.Iio α, Set.range (fun x => (colimit.ι F i) x) := by
  sorry

/-- The cardinality used in the module smallness proposition. -/
def moduleSubmoduleCardinal (R : Type u) [Ring R]
    (M : ModuleCat.{u} R) : Cardinal.{u} :=
  Cardinal.mk (Submodule R (M : Type u))

/-- For modules, a cofinality larger than the cardinality of the submodule set
forces the comparison map to be bijective. -/
theorem module_is_alpha_small
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (α : Ordinal.{u})
    (hα : moduleSubmoduleCardinal R M < Ordinal.cof α) :
    IsAlphaSmall M α (MorphismProperty.monomorphisms (ModuleCat.{u} R)) := by
  sorry

/-! ## Baer's criterion and the first pushout -/

/-- Baer's ideal-extension criterion, using the established module-category
interface `HasIdealExtension`. -/
theorem baer_criterion {R : Type u} [Ring R] (Q : ModuleCat.{u} R) :
    Injective Q ↔ Formalization.Books.MoreAlgebra.Unit55.HasIdealExtension Q := by
  sorry

/-- The module pushout attached to an ideal map `φ : I → M`. -/
noncomputable def idealPushout
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) : ModuleCat.{u} R :=
  pushout (ModuleCat.ofHom I.subtype) φ

/-- The map from `M` into the ideal pushout. -/
noncomputable def idealPushout_inclusion
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) : M ⟶ idealPushout I M φ :=
  pushout.inr (ModuleCat.ofHom I.subtype) φ

/-- The pushout supplies the extension map from `R`. -/
theorem idealPushout_extension
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) :
    ∃ ψ : ModuleCat.of R R ⟶ idealPushout I M φ,
      ModuleCat.ofHom I.subtype ≫ ψ =
        φ ≫ idealPushout_inclusion I M φ := by
  refine ⟨pushout.inl (ModuleCat.ofHom I.subtype) φ, ?_⟩
  exact pushout.condition

/-- Pushout along the ideal inclusion preserves the monomorphism of the
vertical map in the displayed square. -/
theorem idealPushout_inclusion_mono
    {R : Type u} [Ring R] (I : Ideal R) (M : ModuleCat.{u} R)
    (φ : ModuleCat.of R I ⟶ M) :
    Mono (idealPushout_inclusion I M φ) := by
  sorry

/-! ## The huge pushout and its functorial iteration -/

/-- The family of all ideal inclusions `I → R`. -/
def idealInclusionFamily {R : Type u} [Ring R] :
    ∀ I : Ideal R, ModuleCat.of R I ⟶ ModuleCat.of R R :=
  fun I => ModuleCat.ofHom I.subtype

/-- The arrow `M → 0`, used to apply Mathlib's small-object pushout to all
ideal maps into `M`. -/
def moduleZero (R : Type u) [Ring R] : ModuleCat.{u} R := ModuleCat.of R PUnit

def toZeroArrowFunctor (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ Arrow (ModuleCat.{u} R) where
  obj M := Arrow.mk (0 : M ⟶ moduleZero R)
  map f := Arrow.homMk f (𝟙 (moduleZero R)) (by simp)
  map_id := by
    intro M
    ext <;> simp
  map_comp := by
    intro M N P f g
    ext <;> simp

/-- The functorial huge pushout `M ↦ 𝕄(M)`, implemented by the canonical
small-object construction for the family of ideal inclusions. -/
noncomputable def baerStepArrowFunctor (R : Type u) [Ring R] :
    Arrow (ModuleCat.{u} R) ⥤ Arrow (ModuleCat.{u} R) :=
  SmallObject.functor (idealInclusionFamily (R := R))

noncomputable def baerStepFunctor (R : Type u) [Ring R] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  toZeroArrowFunctor R ⋙ baerStepArrowFunctor R ⋙ Arrow.leftFunc

/-- The object `𝕄(M)` in the source's huge pushout diagram. -/
noncomputable def baerStep (R : Type u) [Ring R] (M : ModuleCat.{u} R) :
    ModuleCat.{u} R :=
  (baerStepFunctor R).obj M

/-- The natural map `M → 𝕄(M)` supplied by the pushout construction. -/
noncomputable def baerStepEmbedding (R : Type u) [Ring R] :
    𝟭 (ModuleCat.{u} R) ⟶ baerStepFunctor R where
  app M :=
    SmallObject.ιFunctorObj (idealInclusionFamily (R := R))
      ((toZeroArrowFunctor R).obj M).hom
  naturality M N f := by
    exact (SmallObject.ιFunctorObj_naturality
      (idealInclusionFamily (R := R))
      (τ := (toZeroArrowFunctor R).map f)).symm

/-- The huge pushout extends every map from an ideal. -/
theorem baerStep_ideal_extension
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) (I : Ideal R)
    (φ : ModuleCat.of R I ⟶ M) :
    ∃ ψ : ModuleCat.of R R ⟶ baerStep R M,
      ModuleCat.ofHom I.subtype ≫ ψ =
        φ ≫ (baerStepEmbedding R).app M := by
  sorry

/-- The map into the huge pushout is monomorphic. -/
theorem baerStepEmbedding_mono
    {R : Type u} [Ring R] (M : ModuleCat.{u} R) :
    Mono ((baerStepEmbedding R).app M) := by
  sorry

/-- The successor structure used by the transfinite construction. -/
noncomputable def baerSuccStruct (R : Type u) [Ring R] :
    CategoryTheory.SmallObject.SuccStruct
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  CategoryTheory.SmallObject.SuccStruct.ofNatTrans (baerStepEmbedding R)

/-- The endofunctor at every stage of the ordinal-indexed iteration. -/
noncomputable def baerIterationFunctor (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Set.Iic α ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  (baerSuccStruct R).iterationFunctor (Set.Iic α)

/-- The functor `𝕄_α` at the top stage of the iteration over `α`. -/
noncomputable def baerIteration (R : Type u) [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (baerIterationFunctor R α).obj ⟨α, by simp⟩

/-- The functorial embedding `N → 𝕄_α(N)`. -/
noncomputable def baerIterationEmbedding (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    𝟭 (ModuleCat.{u} R) ⟶ baerIteration R α :=
  ((baerSuccStruct R).ιIterationFunctor (Set.Iic α)).app ⟨α, by simp⟩

/-- The coherent diagram of stages below a limit ordinal. -/
noncomputable def baerIterationDiagram (R : Type u) [Ring R]
    (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Set.Iio α ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{u} R) :=
  (Set.principalSegIioIicOfLE (le_rfl : α ≤ α)).monotone.functor ⋙
    baerIterationFunctor R α

/-- The zero stage is the identity functor. -/
theorem baerIteration_zero {R : Type u} [Ring R]
    [HasIterationOfShape (Set.Iic (0 : Ordinal.{u}))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R 0 ≅
      𝟭 (ModuleCat.{u} R)) := by
  sorry

/-- The first stage is the huge-pushout functor. -/
theorem baerIteration_one {R : Type u} [Ring R]
    [HasIterationOfShape (Set.Iic (1 : Ordinal.{u}))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R 1 ≅ baerStepFunctor R) := by
  sorry

/-- Successor stages are obtained by applying the huge-pushout functor. -/
theorem baerIteration_succ {R : Type u} [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)]
    [HasIterationOfShape (Set.Iic (α + 1))
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)] :
    Nonempty (baerIteration R (α + 1) ≅
      baerIteration R α ⋙ baerStepFunctor R) := by
  sorry

/-- At a limit stage, the iteration is the colimit of its earlier stages. -/
theorem baerIteration_limit {R : Type u} [Ring R] (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)]
    (hα : Order.IsSuccLimit α) :
    Nonempty (baerIteration R α ≅ colimit (baerIterationDiagram R α)) := by
  sorry

/-- The cardinality of the set of ideals of `R`. -/
def idealCardinal (R : Type u) [Ring R] : Cardinal.{u} := Cardinal.mk (Ideal R)

/-- Baer's transfinite construction reaches an injective module at any stage
whose cofinality is larger than the cardinality of the ideal set, and the
canonical map from the starting module is a functorial monomorphic embedding.
-/
theorem baer_grothendieck
    {R : Type u} [Ring R] (N : ModuleCat.{u} R) (α : Ordinal.{u})
    [HasIterationOfShape (Set.Iic α)
      (ModuleCat.{u} R ⥤ ModuleCat.{u} R)]
    (hα : idealCardinal R < Ordinal.cof α) :
    Injective ((baerIteration R α).obj N) ∧
      Mono ((baerIterationEmbedding R α).app N) := by
  sorry

end Formalization.Books.Injectives.Unit02
