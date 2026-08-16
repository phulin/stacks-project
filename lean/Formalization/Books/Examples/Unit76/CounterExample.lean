import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Data.PNat.Notation
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

namespace Formalization.Books.Examples.Unit76

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

theorem originPointV_is_closed (k : Type u) [Field k] :
    IsClosed ({originPointV k} : Set (chartV k)) := by
  exact originPoint_is_closed k

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

/-- Three pairwise distinct indices cannot occur in the two-chart gluing. -/
private theorem no_three_distinct_ulift_bool
    (i j l : ULift.{u} Bool) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  rcases l with ⟨l⟩
  cases i <;> cases j <;> cases l
  all_goals first | exact hij rfl | exact hil rfl | exact hjl rfl

/-- The off-diagonal part of the two-chart gluing datum. -/
noncomputable def counterexampleGlueData' (k : Type u) [Field k] :
    CategoryTheory.GlueData' Scheme.{u} where
  J := ULift.{u} Bool
  U := fun _ => chartU k
  V := fun _ _ _ => (puncturedOpen k).toScheme
  f := fun _ _ _ => (puncturedOpen k).ι
  f_mono := by
    intro i j h
    infer_instance
  f_hasPullback := by
    intro i j l hij hil
    infer_instance
  t := fun _ _ _ => 𝟙 (puncturedOpen k).toScheme
  t' := by
    intro i j l hij hil hjl
    exact (no_three_distinct_ulift_bool i j l hij hil hjl).elim
  t_fac := by
    intro i j l hij hil hjl
    exact (no_three_distinct_ulift_bool i j l hij hil hjl).elim
  t_inv := by
    intro i j hij
    simp
  cocycle := by
    intro i j l hij hil hjl
    exact (no_three_distinct_ulift_bool i j l hij hil hjl).elim

/-- The two-chart gluing datum.  The diagonal intersection is a whole chart,
while the off-diagonal intersection is `U \ {0_U}`. -/
noncomputable abbrev counterexampleGlueData (k : Type u) [Field k] : Scheme.GlueData.{u} :=
  { toGlueData := CategoryTheory.GlueData.ofGlueData' (counterexampleGlueData' k)
    f_open := by
      intro i j
      classical
      change IsOpenImmersion ((counterexampleGlueData' k).f' i j)
      dsimp [CategoryTheory.GlueData'.f']
      split_ifs with h
      · infer_instance
      · exact @IsOpenImmersion.comp _ _ _
          (eqToHom (dif_neg h)) ((counterexampleGlueData' k).f i j h)
          (by infer_instance)
          (by
            change IsOpenImmersion ((puncturedOpen k).ι)
            infer_instance) }

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
  letI : HasMulticoequalizer (counterexampleGlueData k).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (counterexampleGlueData k)
  fapply Multicoequalizer.desc
  · exact fun _ => chartToBase k
  rintro ⟨i, j⟩
  rcases i with ⟨i⟩
  rcases j with ⟨j⟩
  cases i <;> cases j <;>
    simp [CategoryTheory.GlueData.diagram, counterexampleGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      counterexampleGlueData', Category.assoc]

@[simp]
theorem chartInclusion_comp_structureMap (k : Type u) [Field k] (i : Bool) :
    chartInclusion k i ≫ counterexampleStructureMap k = chartToBase k := by
  have hD : HasMulticoequalizer (counterexampleGlueData k).diagram :=
    Scheme.GlueData.instHasMulticoequalizerDiagram (counterexampleGlueData k)
  unfold chartInclusion counterexampleStructureMap
  exact @Multicoequalizer.π_desc _ _ _ (counterexampleGlueData k).diagram hD _ _ _ _

/-! ## Infinitesimal thickenings -/

/-- Positive indices for the thickenings `A_n = A/(t^n)`. -/
abbrev positiveIndex := ℕ+

/-- The ideal `(t^n)` defining the `n`-th thickening of the base. -/
def truncationIdeal (k : Type u) [Field k] (n : positiveIndex) : Ideal (baseRing k) :=
  Ideal.span ({(baseParameter k) ^ (n : ℕ)} : Set (baseRing k))

/-- The quotient ring `A_n = A/(t^n)`. -/
abbrev truncatedBaseRing (k : Type u) [Field k] (n : positiveIndex) :=
  baseRing k ⧸ truncationIdeal k n

/-- The quotient map `A ⟶ A_n`. -/
def truncationMap (k : Type u) [Field k] (n : positiveIndex) :
    baseRing k →+* truncatedBaseRing k n :=
  Ideal.Quotient.mk (truncationIdeal k n)

theorem truncationIdeal_succ_le (k : Type u) [Field k] (n : positiveIndex) :
    truncationIdeal k (n + 1) ≤ truncationIdeal k n := by
  refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
  change (baseParameter k) ^ ((n : ℕ) + 1) ∈ truncationIdeal k n
  exact Ideal.mem_span_singleton'.2 ⟨baseParameter k, by rw [pow_succ, mul_comm]⟩

/-- The quotient map `A_{n+1} ⟶ A_n`. -/
def truncationTransitionMap (k : Type u) [Field k] (n : positiveIndex) :
    truncatedBaseRing k (n + 1) →+* truncatedBaseRing k n :=
  Ideal.Quotient.factor (truncationIdeal_succ_le k n)

/-- The thickening `X_n = X ×_{Spec(A)} Spec(A_n)`. -/
noncomputable def thickening (k : Type u) [Field k] (n : positiveIndex) : Scheme.{u} :=
  pullback (counterexampleStructureMap k)
    (Spec.map (CommRingCat.ofHom (truncationMap k n)))

theorem thickeningInclusion_compat (k : Type u) [Field k] (n : positiveIndex) :
    pullback.fst (counterexampleStructureMap k)
        (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
        counterexampleStructureMap k =
      (pullback.snd (counterexampleStructureMap k)
        (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
        Spec.map (CommRingCat.ofHom (truncationTransitionMap k n))) ≫
        Spec.map (CommRingCat.ofHom (truncationMap k (n + 1))) := by
  sorry

/-- The closed immersion `X_n ⟶ X_{n+1}` induced by `A_{n+1} ⟶ A_n`. -/
noncomputable def thickeningInclusion (k : Type u) [Field k] (n : positiveIndex) :
    thickening k n ⟶ thickening k (n + 1) :=
  pullback.lift
    (pullback.fst (counterexampleStructureMap k)
      (Spec.map (CommRingCat.ofHom (truncationMap k n))))
    (pullback.snd (counterexampleStructureMap k)
      (Spec.map (CommRingCat.ofHom (truncationMap k n))) ≫
      Spec.map (CommRingCat.ofHom (truncationTransitionMap k n)))
    (thickeningInclusion_compat k n)

theorem thickeningInclusion_isClosedImmersion (k : Type u) [Field k] (n : positiveIndex) :
    IsClosedImmersion (thickeningInclusion k n) := by
  sorry

/-- The ring of either affine chart after base change to `A_n`. -/
abbrev thickenedChartRing (k : Type u) [Field k] (n : positiveIndex) :=
  Polynomial (truncatedBaseRing k n)

/-- The first thickened chart `Spec(A_n[x])`. -/
abbrev thickenedChartScheme (k : Type u) [Field k] (n : positiveIndex) : Scheme.{u} :=
  Spec (CommRingCat.of (thickenedChartRing k n))

/-- The base-changed map `A[x] ⟶ A_n[x]`. -/
def chartReductionMap (k : Type u) [Field k] (n : positiveIndex) :
    chartRing k →+* thickenedChartRing k n :=
  Polynomial.mapRingHom (truncationMap k n)

/-- The map from the thickened affine chart to the original chart. -/
noncomputable def thickenedChartToX (k : Type u) [Field k] (n : positiveIndex) (i : Bool) :
    thickenedChartScheme k n ⟶ counterexampleScheme k :=
  Spec.map (CommRingCat.ofHom (chartReductionMap k n)) ≫ chartInclusion k i

/-- The structure map of the thickened affine chart to `Spec(A_n)`. -/
noncomputable def thickenedChartToTruncatedBase (k : Type u) [Field k] (n : positiveIndex) :
    thickenedChartScheme k n ⟶ Spec (CommRingCat.of (truncatedBaseRing k n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (truncatedBaseRing k n)
    (thickenedChartRing k n)))

theorem thickenedChart_maps_compat (k : Type u) [Field k] (n : positiveIndex) (i : Bool) :
    thickenedChartToX k n i ≫ counterexampleStructureMap k =
      thickenedChartToTruncatedBase k n ≫
        Spec.map (CommRingCat.ofHom (truncationMap k n)) := by
  sorry

/-- The canonical chart map into the fiber product `X_n`. -/
noncomputable def thickenedChartToThickening (k : Type u) [Field k] (n : positiveIndex) (i : Bool) :
    thickenedChartScheme k n ⟶ thickening k n :=
  pullback.lift (thickenedChartToX k n i) (thickenedChartToTruncatedBase k n)
    (thickenedChart_maps_compat k n i)

instance thickenedChartToThickening_isOpenImmersion (k : Type u) [Field k] (n : positiveIndex)
    (i : Bool) :
    IsOpenImmersion (thickenedChartToThickening k n i) := by
  sorry

/-! ## The coherent sheaves on the thickenings -/

/-- The quotient module `A_n[x]/(x)` on the first chart. -/
abbrev firstChartModule (k : Type u) [Field k] (n : positiveIndex) :
    ModuleCat (thickenedChartRing k n) :=
  ModuleCat.of (thickenedChartRing k n)
    (thickenedChartRing k n ⧸ Ideal.span ({Polynomial.X} : Set (thickenedChartRing k n)))

/-- The zero module on the second chart. -/
abbrev secondChartModule (k : Type u) [Field k] (n : positiveIndex) :
    ModuleCat (thickenedChartRing k n) :=
  ModuleCat.of (thickenedChartRing k n)
    PUnit

/-- The displayed first-chart module is the finite `A_n`-module `A_n`. -/
theorem firstChartModule_equiv_base (k : Type u) [Field k] (n : positiveIndex) :
    Nonempty ((firstChartModule k n : Type u) ≃ₗ[truncatedBaseRing k n]
      truncatedBaseRing k n) := by
  sorry

/-- The second chart carries the zero module. -/
theorem secondChartModule_is_zero (k : Type u) [Field k] (n : positiveIndex) :
    IsZero (secondChartModule k n) := by
  sorry

/-- A coherent sheaf on a thickening with the two chart restrictions displayed
in the source. -/
structure CoherentThickeningSheaf (k : Type u) [Field k] (n : positiveIndex) where
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
theorem exists_coherentThickeningSheaf (k : Type u) [Field k] (n : positiveIndex) :
    Nonempty (CoherentThickeningSheaf k n) := by
  sorry

/-- The sheaf `𝓕_n` in the source. -/
noncomputable def coherentThickeningSheaf (k : Type u) [Field k] (n : positiveIndex) :
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

/-! The transition maps form an inverse system.  We expose the two-step
coherence explicitly; the usual higher coherences follow from this chosen
system of transition isomorphisms. -/
def CoherentSupportProperSystemTransitionCompatibility (k : Type u) [Field k]
    (sheaves : ∀ n : positiveIndex, CoherentThickeningSheaf k n)
    (transition : ∀ n : positiveIndex,
      (Scheme.Modules.pullback (thickeningInclusion k n)).obj
          (sheaves (n + 1)).sheaf ≅ (sheaves n).sheaf) : Prop :=
  ∀ n : positiveIndex,
    ∃ (comparison :
        (Scheme.Modules.pullback
          (thickeningInclusion k n ≫ thickeningInclusion k (n + 1))).obj
            (sheaves (n + 2)).sheaf ≅
          (Scheme.Modules.pullback (thickeningInclusion k n)).obj
            ((Scheme.Modules.pullback (thickeningInclusion k (n + 1))).obj
              (sheaves (n + 2)).sheaf)),
      ∃ (direct :
        (Scheme.Modules.pullback
          (thickeningInclusion k n ≫ thickeningInclusion k (n + 1))).obj
            (sheaves (n + 2)).sheaf ≅ (sheaves n).sheaf),
        comparison.hom ≫
              (Scheme.Modules.pullback (thickeningInclusion k n)).map
                (transition (n + 1)).hom ≫ (transition n).hom =
          direct.hom

/-- A coherent system with support proper over the base. -/
structure CoherentSupportProperSystem (k : Type u) [Field k] where
  idealSheaf : (counterexampleScheme k).IdealSheafData
  idealSheaf_is_tGenerated : idealSheaf = tGeneratedIdealSheaf k
  sheaves : ∀ n : positiveIndex, CoherentThickeningSheaf k n
  sheaves_are_displayed : ∀ n : positiveIndex, sheaves n = coherentThickeningSheaf k n
  transition : ∀ n : positiveIndex,
    (Scheme.Modules.pullback (thickeningInclusion k n)).obj
        (sheaves (n + 1)).sheaf ≅ (sheaves n).sheaf
  transition_compatible :
    CoherentSupportProperSystemTransitionCompatibility k sheaves transition
  supportProperOverBase : Prop

/-- The displayed system is an object of the source's category
`Coh_support proper over A (X, 𝓘)`. -/
theorem exists_coherentSupportProperSystem (k : Type u) [Field k] :
    Nonempty (CoherentSupportProperSystem k) := by
  sorry

noncomputable def coherentSupportProperSystem (k : Type u) [Field k] :
    CoherentSupportProperSystem k :=
  Classical.choice (exists_coherentSupportProperSystem k)

theorem coherentSupportProperSystem_sheaves_are_displayed
    (k : Type u) [Field k] (n : positiveIndex) :
    (coherentSupportProperSystem k).sheaves n = coherentThickeningSheaf k n :=
  (coherentSupportProperSystem k).sheaves_are_displayed n

/-- Compatibility of the maps `𝒪_{X_n} ⟶ 𝓕_n` after pulling back from the
next thickening.  The two displayed isomorphisms express the canonical
identifications of the pulled-back structure sheaf and of the sheaf system. -/
def StructureSheafSurjectionCompatibility (k : Type u) [Field k]
    (maps : ∀ n : positiveIndex,
      SheafOfModules.unit ((thickening k n).ringCatSheaf) ⟶
        (coherentThickeningSheaf k n).sheaf) : Prop :=
  ∀ n : positiveIndex,
    ∃ (unitIso :
        (Scheme.Modules.pullback (thickeningInclusion k n)).obj
            (SheafOfModules.unit ((thickening k (n + 1)).ringCatSheaf)) ≅
          SheafOfModules.unit ((thickening k n).ringCatSheaf))
      (sheafIso :
        (Scheme.Modules.pullback (thickeningInclusion k n)).obj
            (coherentThickeningSheaf k (n + 1)).sheaf ≅
          (coherentThickeningSheaf k n).sheaf),
      (Scheme.Modules.pullback (thickeningInclusion k n)).map (maps (n + 1)) ≫
            sheafIso.hom =
        unitIso.hom ≫ maps n

/-- Data of the compatible epimorphisms `𝒪_{X_n} ⟶ 𝓕_n` used in the Quot
argument.  The final field is the compatibility condition in the source's
category of systems. -/
structure StructureSheafSurjectionSystem (k : Type u) [Field k] where
  maps : ∀ n : positiveIndex,
    SheafOfModules.unit ((thickening k n).ringCatSheaf) ⟶
      (coherentThickeningSheaf k n).sheaf
  maps_are_epimorphisms : ∀ n : positiveIndex, Epi (maps n)
  compatible : StructureSheafSurjectionCompatibility k maps

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
    (M : ModuleCat (chartRing k)) (n : positiveIndex) : ModuleCat (chartRing k) := by
  let P := (Ideal.span ({(Polynomial.C (baseParameter k)) ^ (n : ℕ)} : Set (chartRing k))) •
    (⊤ : Submodule (chartRing k) (M : Type u))
  letI : Module (chartRing k) ((M : Type u) ⧸ P) := Submodule.Quotient.module P
  exact ModuleCat.of (chartRing k) ((M : Type u) ⧸ P)

/-- `A_n[x]/(x)`, written as an `A[x]`-module for comparison with reductions. -/
abbrev firstChartReduction (k : Type u) [Field k] (n : positiveIndex) : ModuleCat (chartRing k) :=
  ModuleCat.of (chartRing k)
    (chartRing k ⧸ Ideal.span ({Polynomial.X,
      (Polynomial.C (baseParameter k)) ^ (n : ℕ)} : Set (chartRing k)))

/-- A finite algebraization candidate consists of the two finite chart modules,
their generic-fiber identification, and the prescribed reductions. -/
structure FiniteAlgebraizationCandidate (k : Type u) [Field k] where
  system : CoherentSupportProperSystem k
  M : ModuleCat (chartRing k)
  N : ModuleCat (chartRing k)
  M_finite : Module.Finite (chartRing k) (M : Type u)
  N_finite : Module.Finite (chartRing k) (N : Type u)
  genericFiberIso : Nonempty (localizedChartModule k M ≅ localizedChartModule k N)
  M_reduction : ∀ n : positiveIndex,
    Nonempty (chartModuleQuotient k M n ≅ firstChartReduction k n)
  N_reduction : ∀ n : positiveIndex, IsZero (chartModuleQuotient k N n)

/-- The source's completion-functor image condition for a specified coherent
system. -/
def InCompletionFunctorImage (k : Type u) [Field k]
    (𝓕 : CoherentSupportProperSystem k) : Prop :=
  ∃ C : FiniteAlgebraizationCandidate k, C.system = 𝓕

/-- Unpacking an image under the completion functor produces exactly the
finite chart modules and comparison data displayed in the source. -/
theorem completionFunctorImage_gives_finite_algebraization
    (k : Type u) [Field k] (𝓕 : CoherentSupportProperSystem k)
    (h𝓕 : InCompletionFunctorImage k 𝓕) :
    ∃ M N : ModuleCat (chartRing k),
      Module.Finite (chartRing k) (M : Type u) ∧
        Module.Finite (chartRing k) (N : Type u) ∧
          Nonempty (localizedChartModule k M ≅ localizedChartModule k N) ∧
            (∀ n : positiveIndex,
              Nonempty (chartModuleQuotient k M n ≅ firstChartReduction k n)) ∧
              (∀ n : positiveIndex, IsZero (chartModuleQuotient k N n)) := by
  rcases h𝓕 with ⟨C, hC⟩
  subst hC
  exact ⟨C.M, C.N, C.M_finite, C.N_finite, C.genericFiberIso,
    C.M_reduction, C.N_reduction⟩

/-- The displayed compatible system is not in the image of the completion
functor from coherent sheaves with proper support. -/
theorem coherentSupportProperSystem_not_in_completionFunctor_image
    (k : Type u) [Field k] :
    ¬ InCompletionFunctorImage k (coherentSupportProperSystem k) := by
  sorry

/-! ## The three consequences recorded in the source -/

/-- The completion-functor assertion whose failure is the first consequence
of the displayed non-algebraizable system. -/
def GrothendieckExistenceWithoutSeparatedness (k : Type u) [Field k] : Prop :=
  InCompletionFunctorImage k (coherentSupportProperSystem k)

theorem grothendieck_existence_theorem_without_separatedness_fails
    (k : Type u) [Field k] :
    ¬ GrothendieckExistenceWithoutSeparatedness k := by
  exact coherentSupportProperSystem_not_in_completionFunctor_image k

/-- The separatedness hypothesis is essential in the cited form of
Grothendieck's existence theorem. -/
theorem grothendieck_existence_false_without_separatedness (k : Type u) [Field k] :
    ¬ IsSeparated (counterexampleStructureMap k) := by
  sorry

/-- The part of an algebraicity witness for the coherent-sheaf stack supplied
by Artin's effectivity axiom.  Mathlib has no stack-of-coherent-sheaves object,
so this is the chapter-facing algebraicity interface. -/
structure CoherentSheafStackAlgebraicityData (k : Type u) [Field k] where
  isAlgebraic : Prop
  effectivity : isAlgebraic →
    InCompletionFunctorImage k (coherentSupportProperSystem k)

def CoherentSheafStackIsAlgebraic (k : Type u) [Field k] : Prop :=
  ∃ D : CoherentSheafStackAlgebraicityData k, D.isAlgebraic

theorem coherentSheafStack_not_algebraic_without_separatedness
    (k : Type u) [Field k] :
    ¬ CoherentSheafStackIsAlgebraic k := by
  rintro ⟨D, hD⟩
  exact coherentSupportProperSystem_not_in_completionFunctor_image k
    (D.effectivity hD)

/-- The failure of Artin's effectivity axiom for the coherent-sheaf stack in
this counterexample. -/
def CoherentSheafStackArtinAxiomFourFails (k : Type u) [Field k] : Prop :=
  ¬ InCompletionFunctorImage k (coherentSupportProperSystem k)

theorem coherentSheafStack_artinAxiomFour_fails (k : Type u) [Field k] :
    CoherentSheafStackArtinAxiomFourFails k :=
  coherentSupportProperSystem_not_in_completionFunctor_image k

/-- The part of an algebraic-space witness for the Quot functor that Artin's
effectivity argument uses. -/
structure QuotFunctorAlgebraicityData (k : Type u) [Field k] where
  isAlgebraicSpace : Prop
  effectivity : isAlgebraicSpace →
    InCompletionFunctorImage k (coherentSupportProperSystem k)
  compatibleSurjections : Nonempty (StructureSheafSurjectionSystem k)

def QuotFunctorIsAlgebraicSpace (k : Type u) [Field k] : Prop :=
  ∃ D : QuotFunctorAlgebraicityData k, D.isAlgebraicSpace

theorem quotFunctor_not_algebraicSpace_without_separatedness
    (k : Type u) [Field k] :
    ¬ QuotFunctorIsAlgebraicSpace k := by
  rintro ⟨D, hD⟩
  exact coherentSupportProperSystem_not_in_completionFunctor_image k
    (D.effectivity hD)

/-- The failure of the corresponding effectivity axiom for the Quot functor.
-/
def QuotFunctorArtinAxiomFourFails (k : Type u) [Field k] : Prop :=
  ¬ InCompletionFunctorImage k (coherentSupportProperSystem k)

theorem quotFunctor_artinAxiomFour_fails (k : Type u) [Field k] :
    QuotFunctorArtinAxiomFourFails k :=
  coherentSupportProperSystem_not_in_completionFunctor_image k

theorem counterexamples_to_algebraization (k : Type u) [Field k] :
    ¬ IsSeparated (counterexampleStructureMap k) ∧
      ¬ CoherentSheafStackIsAlgebraic k ∧
        ¬ QuotFunctorIsAlgebraicSpace k := by
  exact ⟨grothendieck_existence_false_without_separatedness k,
    coherentSheafStack_not_algebraic_without_separatedness k,
    quotFunctor_not_algebraicSpace_without_separatedness k⟩

end Formalization.Books.Examples.Unit76
