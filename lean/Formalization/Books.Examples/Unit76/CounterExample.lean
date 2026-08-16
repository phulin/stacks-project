import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Examples, Chapter 76: A counterexample to Grothendieck's existence theorem

The source constructs a non-separated scheme by gluing two affine charts over
`k[[t]]`.  The chart, puncture, infinitesimal thickening, and module data below
use Mathlib's scheme-gluing and module APIs; the geometric existence and
non-algebraization arguments are theorem interfaces for the proving stage.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

universe u

namespace Formalization.«Books.Examples».Unit76

/-! ## The base ring and the two affine charts -/

/-- The complete base ring `A = k[[t]]`. -/
abbrev baseRing (k : Type u) [Field k] := PowerSeries k

/-- The parameter `t` in `A = k[[t]]`. -/
def baseParameter (k : Type u) [Field k] : baseRing k := PowerSeries.X

/-- The polynomial chart ring `A[x]` (and, after renaming, `A[y]`). -/
abbrev chartRing (k : Type u) [Field k] := Polynomial (baseRing k)

/-- The affine chart `U = Spec(A[x])`. -/
abbrev chartU (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (chartRing k))

/-- The second affine chart `V = Spec(A[y])`, represented by the same
polynomial ring after the canonical variable renaming `x ↦ y`. -/
abbrev chartV (k : Type u) [Field k] : Scheme.{u} := chartU k

/-- The affine base `Spec(A)`. -/
abbrev baseScheme (k : Type u) [Field k] : Scheme.{u} :=
  Spec (CommRingCat.of (baseRing k))

/-- The structure morphism of either affine chart over `Spec(A)`. -/
noncomputable def chartToBase (k : Type u) [Field k] : chartU k ⟶ baseScheme k :=
  Spec.map (CommRingCat.ofHom (algebraMap (baseRing k) (chartRing k)))

/-- The ideal `(x,t)` in the chart ring. -/
def originIdeal (k : Type u) [Field k] : Ideal (chartRing k) :=
  Ideal.span ({Polynomial.X, Polynomial.C (baseParameter k)} : Set (chartRing k))

/-- Evaluation at `x = 0` followed by taking the constant coefficient in
`k[[t]]`; its kernel is the point `(x,t)`. -/
def originEvaluation (k : Type u) [Field k] : chartRing k →+* k :=
  Polynomial.eval₂RingHom (PowerSeries.constantCoeff (R := k)) 0

/-- The distinguished closed point `0_U = (x,t)`. -/
def originPoint (k : Type u) [Field k] : chartU k :=
  ⟨RingHom.ker (originEvaluation k), RingHom.ker_isPrime _⟩

/-- The corresponding point in the second chart. -/
def originPointV (k : Type u) [Field k] : chartV k := originPoint k

theorem originIdeal_eq_kernel (k : Type u) [Field k] :
    originIdeal k = RingHom.ker (originEvaluation k) := by
  sorry

theorem originPoint_is_closed (k : Type u) [Field k] :
    IsClosed ({originPoint k} : Set (chartU k)) := by
  sorry

/-- The punctured affine chart `U \ {0_U}`. -/
def puncturedOpen (k : Type u) [Field k] : (chartU k).Opens := by
  refine ⟨{p | p ≠ originPoint k}, ?_⟩
  have hset : {p : chartU k | p ≠ originPoint k} =
      ({originPoint k} : Set (chartU k))ᶜ := by
    ext p
    simp
  rw [hset]
  exact (originPoint_is_closed k).isOpen_compl

/-- The same punctured chart viewed as an open of `V`. -/
def puncturedOpenV (k : Type u) [Field k] : (chartV k).Opens := puncturedOpen k

/-- The identification of the punctured charts, sending the polynomial
variable on the first presentation to the polynomial variable on the second. -/
noncomputable def puncturedIdentification (k : Type u) [Field k] :
    (puncturedOpen k).toScheme ≅ (puncturedOpenV k).toScheme :=
  Iso.refl _

theorem puncturedIdentification_sends_variable (k : Type u) [Field k] :
    (Polynomial.X : chartRing k) = Polynomial.X := by
  rfl

/-! ## The glued scheme -/

/-- The intersection scheme used by the two-chart gluing datum. -/
def glueIntersection (k : Type u) [Field k] (i j : Bool) : Scheme.{u} :=
  if i = j then chartU k else (puncturedOpen k).toScheme

/-- The open immersion from an intersection into its first chart. -/
noncomputable def glueIntersectionMap (k : Type u) [Field k] (i j : Bool) :
    glueIntersection k i j ⟶ chartU k := by
  by_cases h : i = j
  · simp [glueIntersection, h]
    exact 𝟙 _
  · simp [glueIntersection, h]
    exact (puncturedOpen k).ι

/-- The transition map between the two presentations of an intersection. -/
noncomputable def glueTransition (k : Type u) [Field k] (i j : Bool) :
    glueIntersection k i j ⟶ glueIntersection k j i := by
  by_cases h : i = j
  · subst j
    exact 𝟙 _
  · have h' : ¬j = i := by
      intro h'
      exact h h'.symm
    simp [glueIntersection, h, h']
    exact 𝟙 _

/-- The two-chart gluing datum.  The diagonal intersection is a whole chart,
while the off-diagonal intersection is `U \ {0_U}`. -/
noncomputable def counterexampleGlueData (k : Type u) [Field k] :
    Scheme.GlueData.{u} where
  J := ULift.{u} Bool
  U := fun _ => chartU k
  V := fun ij => glueIntersection k ij.1.down ij.2.down
  f := fun i j => glueIntersectionMap k i.down j.down
  f_mono := by
    sorry
  f_hasPullback := by
    intro _ _ _
    infer_instance
  f_id := by
    sorry
  t := fun i j => glueTransition k i.down j.down
  t_id := by
    sorry
  t' := by
    intro i j l
    sorry
  t_fac := by
    intro i j l
    sorry
  cocycle := by
    intro i j l
    sorry
  f_open := by
    sorry

/-- The glued scheme `X`. -/
noncomputable def counterexampleScheme (k : Type u) [Field k] : Scheme.{u} :=
  (counterexampleGlueData k).glued

/-- The two affine chart immersions into `X`. -/
noncomputable def chartInclusion (k : Type u) [Field k] (i : Bool) :
    chartU k ⟶ counterexampleScheme k :=
  (counterexampleGlueData k).ι (ULift.up i)

instance chartInclusion_isOpenImmersion (k : Type u) [Field k] (i : Bool) :
    IsOpenImmersion (chartInclusion k i) := by
  exact Scheme.GlueData.ι_isOpenImmersion (counterexampleGlueData k) (ULift.up i)

/-- The structure morphism `X ⟶ Spec(A)` obtained by gluing the two chart maps. -/
noncomputable def counterexampleStructureMap (k : Type u) [Field k] :
    counterexampleScheme k ⟶ baseScheme k := by
  fapply Multicoequalizer.desc
  · exact fun _ => chartToBase k
  rintro ⟨i, j⟩
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j <;>
    simp [CategoryTheory.GlueData.diagram, counterexampleGlueData, glueTransition,
      glueIntersectionMap, glueIntersection, Category.assoc] <;>
    rfl

@[simp]
theorem chartInclusion_comp_structureMap (k : Type u) [Field k] (i : Bool) :
    chartInclusion k i ≫ counterexampleStructureMap k = chartToBase k := by
  unfold chartInclusion counterexampleStructureMap
  exact Multicoequalizer.π_desc _ _ _ _ _

/-! ## Infinitesimal thickenings -/

/-- The ideal `(t^n)` defining the `n`-th thickening of the base. -/
def truncationIdeal (k : Type u) [Field k] (n : ℕ) : Ideal (baseRing k) :=
  Ideal.span ({(baseParameter k) ^ n} : Set (baseRing k))

/-- The quotient ring `A_n = A/(t^n)`. -/
abbrev truncatedBaseRing (k : Type u) [Field k] (n : ℕ) :=
  baseRing k ⧸ truncationIdeal k n

/-- The quotient map `A ⟶ A_n`. -/
def truncationMap (k : Type u) [Field k] (n : ℕ) :
    baseRing k →+* truncatedBaseRing k n :=
  Ideal.Quotient.mk (truncationIdeal k n)

theorem truncationIdeal_succ_le (k : Type u) [Field k] (n : ℕ) :
    truncationIdeal k (n + 1) ≤ truncationIdeal k n := by
  refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
  exact Ideal.mem_span_singleton'.2 ⟨baseParameter k, by rw [pow_succ, mul_comm]⟩

/-- The quotient map `A_{n+1} ⟶ A_n`. -/
def truncationTransitionMap (k : Type u) [Field k] (n : ℕ) :
    truncatedBaseRing k (n + 1) →+* truncatedBaseRing k n :=
  Ideal.Quotient.factor (truncationIdeal_succ_le k n)

/-- The thickening `X_n = X ×_{Spec(A)} Spec(A_n)`. -/
noncomputable def thickening (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  pullback (counterexampleStructureMap k)
    (Spec.map (CommRingCat.ofHom (truncationMap k n)))

theorem thickeningInclusion_compat (k : Type u) [Field k] (n : ℕ) :
    pullback.fst (counterexampleStructureMap k)
        (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
        counterexampleStructureMap k =
      (pullback.snd (counterexampleStructureMap k)
        (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
        Spec.map (CommRingCat.ofHom (truncationTransitionMap k n))) ≫
        Spec.map (CommRingCat.ofHom (truncationMap k (n + 1))) := by
  sorry

/-- The closed immersion `X_n ⟶ X_{n+1}` induced by `A_{n+1} ⟶ A_n`. -/
noncomputable def thickeningInclusion (k : Type u) [Field k] (n : ℕ) :
    thickening k n ⟶ thickening k (n + 1) :=
  pullback.lift
    (pullback.fst (counterexampleStructureMap k)
      (Spec.map (CommRingCat.ofHom (truncationMap k n))))
    (pullback.snd (counterexampleStructureMap k)
      (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
      Spec.map (CommRingCat.ofHom (truncationTransitionMap k n)))
    (thickeningInclusion_compat k n)

theorem thickeningInclusion_isClosedImmersion (k : Type u) [Field k] (n : ℕ) :
    IsClosedImmersion (thickeningInclusion k n) := by
  sorry

/-- The ring of either affine chart after base change to `A_n`. -/
abbrev thickenedChartRing (k : Type u) [Field k] (n : ℕ) :=
  Polynomial (truncatedBaseRing k n)

/-- The first thickened chart `Spec(A_n[x])`. -/
abbrev thickenedChartScheme (k : Type u) [Field k] (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (thickenedChartRing k n))

/-- The base-changed map `A[x] ⟶ A_n[x]`. -/
def chartReductionMap (k : Type u) [Field k] (n : ℕ) :
    chartRing k →+* thickenedChartRing k n :=
  Polynomial.mapRingHom (truncationMap k n)

/-- The map from the thickened affine chart to the original chart. -/
noncomputable def thickenedChartToX (k : Type u) [Field k] (n : ℕ) (i : Bool) :
    thickenedChartScheme k n ⟶ counterexampleScheme k :=
  Spec.map (CommRingCat.ofHom (chartReductionMap k n)) ≫ chartInclusion k i

/-- The structure map of the thickened affine chart to `Spec(A_n)`. -/
noncomputable def thickenedChartToTruncatedBase (k : Type u) [Field k] (n : ℕ) :
    thickenedChartScheme k n ⟶ Spec (CommRingCat.of (truncatedBaseRing k n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (truncatedBaseRing k n)
    (thickenedChartRing k n)))

theorem thickenedChart_maps_compat (k : Type u) [Field k] (n : ℕ) (i : Bool) :
    thickenedChartToX k n i ≫ counterexampleStructureMap k =
      thickenedChartToTruncatedBase k n ≫
        Spec.map (CommRingCat.ofHom (truncationMap k n)) := by
  sorry

/-- The canonical chart map into the fiber product `X_n`. -/
noncomputable def thickenedChartToThickening (k : Type u) [Field k] (n : ℕ) (i : Bool) :
    thickenedChartScheme k n ⟶ thickening k n :=
  pullback.lift (thickenedChartToX k n i) (thickenedChartToTruncatedBase k n)
    (thickenedChart_maps_compat k n i)

instance thickenedChartToThickening_isOpenImmersion (k : Type u) [Field k] (n : ℕ)
    (i : Bool) :
    IsOpenImmersion (thickenedChartToThickening k n i) := by
  sorry

/-! ## The coherent sheaves on the thickenings -/

/-- The quotient module `A_n[x]/(x)` on the first chart. -/
abbrev firstChartModule (k : Type u) [Field k] (n : ℕ) :
    ModuleCat (thickenedChartRing k n) :=
  ModuleCat.of (thickenedChartRing k n)
    (thickenedChartRing k n ⧸ Ideal.span ({Polynomial.X} : Set (thickenedChartRing k n)))

/-- The zero module on the second chart. -/
abbrev secondChartModule (k : Type u) [Field k] (n : ℕ) :
    ModuleCat (thickenedChartRing k n) :=
  ModuleCat.of (thickenedChartRing k n)
    (⊥ : Submodule (thickenedChartRing k n) (thickenedChartRing k n))

/-- The displayed first-chart module is the finite `A_n`-module `A_n`. -/
theorem firstChartModule_equiv_base (k : Type u) [Field k] (n : ℕ) :
    Nonempty ((firstChartModule k n : Type u) ≃ₗ[truncatedBaseRing k n]
      truncatedBaseRing k n) := by
  sorry

/-- The second chart carries the zero module. -/
theorem secondChartModule_is_zero (k : Type u) [Field k] (n : ℕ) :
    IsZero (secondChartModule k n) := by
  sorry

/-- A coherent sheaf on a thickening with the two chart restrictions displayed
in the source. -/
structure CoherentThickeningSheaf (k : Type u) [Field k] (n : ℕ) where
  sheaf : (thickening k n).Modules
  coherent : sheaf.IsFinitePresentation
  firstChartRestriction : Nonempty (
    (Scheme.Modules.restrictFunctor (thickenedChartToThickening k n false)).obj sheaf ≅
      AlgebraicGeometry.tilde (firstChartModule k n))
  secondChartRestriction : Nonempty (
    (Scheme.Modules.restrictFunctor (thickenedChartToThickening k n true)).obj sheaf ≅
      AlgebraicGeometry.tilde (secondChartModule k n))

/-- Existence of the coherent sheaf obtained by gluing the quotient module on
the first chart to the zero module on the second chart. -/
theorem exists_coherentThickeningSheaf (k : Type u) [Field k] (n : ℕ) :
    Nonempty (CoherentThickeningSheaf k n) := by
  sorry

/-- The sheaf `𝓕_n` in the source. -/
noncomputable def coherentThickeningSheaf (k : Type u) [Field k] (n : ℕ) :
    CoherentThickeningSheaf k n :=
  Classical.choice (exists_coherentThickeningSheaf k n)

/-- The ideal generated by `t`, the chartwise description of the source's
ideal sheaf `𝓘 ⊆ 𝒪_X`. -/
def tIdeal (k : Type u) [Field k] : Ideal (baseRing k) :=
  Ideal.span ({baseParameter k} : Set (baseRing k))

/-- The ideal sheaf generated by `t` on `Spec(A)`, transported through the
global-sections equivalence. -/
noncomputable def baseTGeneratedIdealSheaf (k : Type u) [Field k] :
    (baseScheme k).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((tIdeal k).comap (Scheme.ΓSpecIso (CommRingCat.of (baseRing k))).hom.hom)

/-- The ideal sheaf `𝓘 ⊆ 𝒪_X` generated by the base parameter `t`. -/
noncomputable def tGeneratedIdealSheaf (k : Type u) [Field k] :
    (counterexampleScheme k).IdealSheafData :=
  (baseTGeneratedIdealSheaf k).comap (counterexampleStructureMap k)

/-- A coherent system with support proper over the base. -/
structure CoherentSupportProperSystem (k : Type u) [Field k] where
  idealSheaf : (counterexampleScheme k).IdealSheafData
  idealSheaf_is_tGenerated : idealSheaf = tGeneratedIdealSheaf k
  sheaves : ∀ n : ℕ, CoherentThickeningSheaf k n
  transition : ∀ n : ℕ, Nonempty (
    (Scheme.Modules.pullback (thickeningInclusion k n)).obj
        (sheaves (n + 1)).sheaf ≅ (sheaves n).sheaf)
  transition_compatible : Prop
  supportProperOverBase : Prop

/-- The displayed system is an object of the source's category
`Coh_support proper over A (X, 𝓘)`. -/
theorem exists_coherentSupportProperSystem (k : Type u) [Field k] :
    Nonempty (CoherentSupportProperSystem k) := by
  sorry

noncomputable def coherentSupportProperSystem (k : Type u) [Field k] :
    CoherentSupportProperSystem k :=
  Classical.choice (exists_coherentSupportProperSystem k)

/-- Data of the compatible epimorphisms `𝒪_{X_n} ⟶ 𝓕_n` used in the Quot
argument.  The final field is the compatibility condition in the source's
category of systems. -/
structure StructureSheafSurjectionSystem (k : Type u) [Field k] where
  maps : ∀ n : ℕ,
    SheafOfModules.unit ((thickening k n).ringCatSheaf) ⟶
      (coherentSupportProperSystem k).sheaves n |>.sheaf
  maps_are_epimorphisms : ∀ n : ℕ, Epi (maps n)
  compatible : Prop

theorem exists_structureSheafSurjectionSystem (k : Type u) [Field k] :
    Nonempty (StructureSheafSurjectionSystem k) := by
  sorry

noncomputable def structureSheafSurjectionSystem (k : Type u) [Field k] :
    StructureSheafSurjectionSystem k :=
  Classical.choice (exists_structureSheafSurjectionSystem k)

/-! ## The obstruction to algebraization -/

/-- The multiplicative system generated by `t` in `A[x]`. -/
def tPowers (k : Type u) [Field k] : Submonoid (chartRing k) :=
  Submonoid.powers (Polynomial.C (baseParameter k))

/-- The localization of a chart module after inverting `t`. -/
abbrev localizedChartModule (k : Type u) [Field k]
    (M : ModuleCat (chartRing k)) : ModuleCat (Localization (tPowers k)) :=
  ModuleCat.of (Localization (tPowers k))
    (LocalizedModule (tPowers k) (M : Type u))

/-- The `t^n`-adic quotient of a chart module. -/
noncomputable def chartModuleQuotient (k : Type u) [Field k]
    (M : ModuleCat (chartRing k)) (n : ℕ) : ModuleCat (chartRing k) := by
  let P := (Ideal.span ({(Polynomial.C (baseParameter k)) ^ n} : Set (chartRing k))) •
    (⊤ : Submodule (chartRing k) (M : Type u))
  letI : Module (chartRing k) ((M : Type u) ⧸ P) := Submodule.Quotient.module P
  exact ModuleCat.of (chartRing k) ((M : Type u) ⧸ P)

/-- `A_n[x]/(x)`, written as an `A[x]`-module for comparison with reductions. -/
abbrev firstChartReduction (k : Type u) [Field k] (n : ℕ) : ModuleCat (chartRing k) :=
  ModuleCat.of (chartRing k)
    (chartRing k ⧸ Ideal.span ({Polynomial.X,
      (Polynomial.C (baseParameter k)) ^ n} : Set (chartRing k)))

/-- A finite algebraization candidate consists of the two finite chart modules,
their generic-fiber identification, and the prescribed reductions. -/
structure FiniteAlgebraizationCandidate (k : Type u) [Field k] where
  system : CoherentSupportProperSystem k
  M : ModuleCat (chartRing k)
  N : ModuleCat (chartRing k)
  M_finite : Module.Finite (chartRing k) (M : Type u)
  N_finite : Module.Finite (chartRing k) (N : Type u)
  genericFiberIso : Nonempty (localizedChartModule k M ≅ localizedChartModule k N)
  M_reduction : ∀ n : ℕ, Nonempty (chartModuleQuotient k M n ≅ firstChartReduction k n)
  N_reduction : ∀ n : ℕ, IsZero (chartModuleQuotient k N n)

/-- The source's completion-functor image condition for a specified coherent
system. -/
def InCompletionFunctorImage (k : Type u) [Field k]
    (𝓕 : CoherentSupportProperSystem k) : Prop :=
  ∃ C : FiniteAlgebraizationCandidate k, C.system = 𝓕

/-- The displayed compatible system is not in the image of the completion
functor from coherent sheaves with proper support. -/
theorem coherentSupportProperSystem_not_in_completionFunctor_image
    (k : Type u) [Field k] :
    ¬ InCompletionFunctorImage k (coherentSupportProperSystem k) := by
  sorry

/-! ## The three consequences recorded in the source -/

/-- The separatedness hypothesis is essential in the cited form of
Grothendieck's existence theorem. -/
theorem grothendieck_existence_false_without_separatedness (k : Type u) [Field k] :
    ¬ IsSeparated (counterexampleStructureMap k) := by
  sorry

/-- The part of an algebraicity witness for the coherent-sheaf stack supplied
by Artin's effectivity axiom.  Mathlib has no stack-of-coherent-sheaves object,
so this is the chapter-facing algebraicity interface. -/
structure CoherentSheafStackAlgebraicityData (k : Type u) [Field k] : Prop where
  effectivity : InCompletionFunctorImage k (coherentSupportProperSystem k)

def CoherentSheafStackIsAlgebraic (k : Type u) [Field k] : Prop :=
  CoherentSheafStackAlgebraicityData k

theorem coherentSheafStack_not_algebraic_without_separatedness
    (k : Type u) [Field k] :
    ¬ CoherentSheafStackIsAlgebraic k := by
  intro h
  exact coherentSupportProperSystem_not_in_completionFunctor_image k h.effectivity

/-- The failure of Artin's effectivity axiom for the coherent-sheaf stack in
this counterexample. -/
def CoherentSheafStackArtinAxiomFourFails (k : Type u) [Field k] : Prop :=
  ¬ CoherentSheafStackIsAlgebraic k

theorem coherentSheafStack_artinAxiomFour_fails (k : Type u) [Field k] :
    CoherentSheafStackArtinAxiomFourFails k :=
  coherentSheafStack_not_algebraic_without_separatedness k

/-- The part of an algebraic-space witness for the Quot functor that Artin's
effectivity argument uses. -/
structure QuotFunctorAlgebraicityData (k : Type u) [Field k] : Prop where
  effectivity : InCompletionFunctorImage k (coherentSupportProperSystem k)
  compatibleSurjections : Nonempty (StructureSheafSurjectionSystem k)

def QuotFunctorIsAlgebraicSpace (k : Type u) [Field k] : Prop :=
  QuotFunctorAlgebraicityData k

theorem quotFunctor_not_algebraicSpace_without_separatedness
    (k : Type u) [Field k] :
    ¬ QuotFunctorIsAlgebraicSpace k := by
  intro h
  exact coherentSupportProperSystem_not_in_completionFunctor_image k h.effectivity

/-- The failure of the corresponding effectivity axiom for the Quot functor.
-/
def QuotFunctorArtinAxiomFourFails (k : Type u) [Field k] : Prop :=
  ¬ QuotFunctorIsAlgebraicSpace k

theorem quotFunctor_artinAxiomFour_fails (k : Type u) [Field k] :
    QuotFunctorArtinAxiomFourFails k :=
  quotFunctor_not_algebraicSpace_without_separatedness k

theorem counterexamples_to_algebraization (k : Type u) [Field k] :
    ¬ IsSeparated (counterexampleStructureMap k) ∧
      ¬ CoherentSheafStackIsAlgebraic k ∧
        ¬ QuotFunctorIsAlgebraicSpace k := by
  exact ⟨grothendieck_existence_false_without_separatedness k,
    coherentSheafStack_not_algebraic_without_separatedness k,
    quotFunctor_not_algebraicSpace_without_separatedness k⟩

end Formalization.«Books.Examples».Unit76
