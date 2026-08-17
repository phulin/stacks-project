import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Formalization.Books.MoreAlgebra.Unit04.CommentOnArtinRees
import Formalization.Books.MoreAlgebra.Unit36.TopologicalRings
import Formalization.Books.Sheaves.Unit20.SheafificationOfPresheavesOfModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Data.PNat.Basic
import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Cohomology of Sheaves, Chapter 28: inverse systems and cohomology, I

The source works with inverse systems of sheaves of modules and their
cohomology.  The canonical category of sheaves of modules over a fixed ring
is `SheafOfModules`; here the fixed ring is the constant sheaf associated to
`A`.  The quotient sheaves `I ^ n F_{m+1}` are kept as explicit data.  This
matches the source's use of those objects while avoiding a second, parallel
construction of submodules in a sheaf category.
-/

namespace Formalization.Books.Cohomology.Unit28

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Formalization.Books.Algebra.Unit86
open Formalization.Books.Categories.Unit21
open Formalization.Books.Homology.Unit12
open Formalization.Books.MoreAlgebra.Unit04
open Formalization.Books.Sheaves.Unit20
open scoped DirectSum

universe v

noncomputable section

/-! ## The source's sheaf and inverse-system data -/

/-- The constant sheaf of commutative rings attached to `A`. -/
abbrev constantCommRingSheaf (X : TopCat.{v}) (A : Type v) [CommRing A] :
    CommRingSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) CommRingCat).obj
    (CommRingCat.of A)

/-- Sheaves of modules over the constant sheaf associated to `A`. -/
abbrev SheafOfAModules (A : Type v) (X : TopCat.{v}) [CommRing A] :=
  CommRingSheafModule (constantCommRingSheaf X A)

/-- The positive stage `F_{n+1}` corresponding to the degree `n` power. -/
def positiveStage (n : ℕ) : ℕ+ :=
  ⟨n + 1, Nat.succ_pos n⟩

/-- The positive stage `F_n` when `n` is positive. -/
def positiveStageOfPositive (n : ℕ) (hn : 0 < n) : ℕ+ :=
  ⟨n, hn⟩

/-- The transition morphism from stage `m` to stage `n` of an inverse system. -/
def stageMap {A : Type v} {X : TopCat.{v}} [CommRing A]
    (F : InverseSystem ℕ+ (SheafOfAModules A X))
    {n m : ℕ+} (h : n ≤ m) : F.obj (op m) ⟶ F.obj (op n) :=
  F.map (opHomOfLE h)

/-- The inequality needed for the map `F_{m+1} ⟶ F_n` when `n > 0`. -/
theorem positiveStageOfPositive_le_stage
    {n m : ℕ} (hn : 0 < n) (h : n ≤ m) :
    positiveStageOfPositive n hn ≤ positiveStage m := by
  change n ≤ m + 1
  exact Nat.le_trans h (Nat.le_succ m)

/--
An inverse system together with the objects denoted by `I ^ n F_{m+1}` in the
source.

The fields `powerToBase_comp` and `powerToStage_zero` record the displayed
transition diagram and the vanishing composite.  `shortExact` records the
source's exact sequence
`0 ⟶ I ^ n F_{m+1} ⟶ F_{m+1} ⟶ F_n ⟶ 0` for every positive `n ≤ m`.
-/
structure IAdicSheafSystem
    (A : Type v) [CommRing A] (X : TopCat.{v}) (I : Ideal A) where
  stages : InverseSystem ℕ+ (SheafOfAModules A X)
  power : ∀ n m : ℕ, n ≤ m → SheafOfAModules A X
  powerToStage : ∀ (n m : ℕ) (h : n ≤ m),
    power n m h ⟶ stages.obj (op (positiveStage m))
  powerToBase : ∀ (n m : ℕ) (h : n ≤ m),
    power n m h ⟶ power n n le_rfl
  powerToBase_comp : ∀ (n m : ℕ) (hn : 0 < n) (h : n ≤ m),
    powerToBase n m h ≫ powerToStage n n le_rfl ≫
        stages.map (opHomOfLE
          (positiveStageOfPositive_le_stage hn le_rfl)) =
      powerToStage n m h ≫ stages.map (opHomOfLE
        (positiveStageOfPositive_le_stage hn h))
  powerToStage_zero : ∀ (n m : ℕ) (hn : 0 < n) (h : n ≤ m),
    powerToStage n m h ≫ stages.map (opHomOfLE
      (positiveStageOfPositive_le_stage hn h)) = 0
  shortExact : ∀ (n m : ℕ) (hn : 0 < n) (h : n ≤ m),
    (ShortComplex.mk
      (powerToStage n m h)
      (stages.map (opHomOfLE
        (positiveStageOfPositive_le_stage hn h)))
      (powerToStage_zero n m hn h)).ShortExact

/-- The short exact sequence attached to a power object and two stages. -/
def adicPowerShortComplex
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (S : IAdicSheafSystem A X I) (n m : ℕ) (hn : 0 < n) (h : n ≤ m) :
    ShortComplex (SheafOfAModules A X) :=
  ShortComplex.mk
    (S.powerToStage n m h)
    (S.stages.map (opHomOfLE
      (positiveStageOfPositive_le_stage hn h)))
    (S.powerToStage_zero n m hn h)

theorem adicPowerShortComplex_shortExact
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (S : IAdicSheafSystem A X I) (n m : ℕ) (hn : 0 < n) (h : n ≤ m) :
    (adicPowerShortComplex S n m hn h).ShortExact := by
  simpa [adicPowerShortComplex] using S.shortExact n m hn h

/-! ## Cohomology systems and the two source versions of `N_n` -/

/-- A cohomological delta-functor with values in `A`-modules. -/
abbrev SheafCohomologicalDeltaFunctor
    (A : Type v) [CommRing A] (X : TopCat.{v}) :=
  CohomologicalDeltaFunctor
    (SheafOfAModules A X) (ModuleCat.{v} A)

/-- The inverse system `n ↦ H^p(X,F_n)`. -/
abbrev cohomologySystem
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) :
    InverseSystem ℕ+ (ModuleCat.{v} A) :=
  S.stages ⋙ H.functor p

/-- The source's Mittag--Leffler condition, using Mathlib's canonical API. -/
abbrev cohomologySystemIsMittagLeffler
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : Prop :=
  IsMittagLefflerModuleSystem (cohomologySystem H S p)

/--
The stronger, uniform stable-image assertion in the first two source
footnotes.  The image from stage `n` to stage `n - c` is required to equal
Mathlib's eventual-range submodule at stage `n - c`.
-/
def positiveStageSub (n : ℕ+) (c : ℕ) (h : c < (n : ℕ)) : ℕ+ :=
  ⟨(n : ℕ) - c, Nat.sub_pos_of_lt h⟩

theorem positiveStageSub_le (n : ℕ+) (c : ℕ) (h : c < (n : ℕ)) :
    positiveStageSub n c h ≤ n := by
  change (n : ℕ) - c ≤ (n : ℕ)
  exact Nat.sub_le _ _

def inverseSystemHasUniformStableImage
    {A : Type v} [CommRing A]
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ+, ∀ h : c < (n : ℕ),
    LinearMap.range (((M.map (opHomOfLE
      (positiveStageSub_le n c h))).hom)) =
      moduleEventualRange M (op (positiveStageSub n c h))

/-- The uniform stable-image assertion for a cohomology system. -/
abbrev cohomologySystemHasUniformStableImage
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : Prop :=
  inverseSystemHasUniformStableImage (cohomologySystem H S p)

/-- The connecting morphism for the exact sequence at indices `n ≤ m`. -/
def cohomologyBoundary
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (n : ℕ+) (m : ℕ)
    (h : (n : ℕ) ≤ m) (p : ℕ) :
    (H.functor p).obj (S.stages.obj (op n)) ⟶
      (H.functor (p + 1)).obj (S.power (n : ℕ) m h) :=
  H.delta (adicPowerShortComplex S (n : ℕ) m n.2 h)
    (adicPowerShortComplex_shortExact S (n : ℕ) m n.2 h) p

/-- The degree-`p` family `H^p(X,I^n F_{n+1})`. -/
abbrev powerCohomologyModuleFamily
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : ℕ → ModuleCat.{v} A :=
  fun n => (H.functor p).obj (S.power n n le_rfl)

/-- The `m`-th image in the source's definition of the stable `N_n`. -/
def powerCohomologyImage
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p n : ℕ)
    (m : {m : ℕ // n ≤ m}) :
    Submodule A ((powerCohomologyModuleFamily H S p n : Type v)) :=
  LinearMap.range (((H.functor p).map
    (S.powerToBase n m.1 m.2)).hom)

/--
The stable-image submodule
`N_n = ⋂_{m≥n} Im(H^p(X,I^nF_{m+1}) → H^p(X,I^nF_{n+1}))`.

This is the module-valued version of the source's intersection; the
underlying set is obtained by coercion to `Set`.
-/
def stablePowerCohomologySubmodule
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p n : ℕ) :
    Submodule A ((powerCohomologyModuleFamily H S p n : Type v)) :=
  ⨅ m : {m : ℕ // n ≤ m}, powerCohomologyImage H S p n m

/-- The stable-image family `n ↦ N_n` as `A`-modules. -/
def stablePowerCohomologyModuleFamily
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : ℕ → ModuleCat.{v} A :=
  fun n => ModuleCat.of A (stablePowerCohomologySubmodule H S p n : Type v)

/-! ## The graded ACC hypothesis -/

/--
The source's phrase “satisfies ACC as a graded module”, expressed with the
existing associated graded ring and Mathlib's `IsNoetherian` predicate.

The explicit `DirectSum.Gmodule` argument is the degree-preserving action that
the source uses in its multiplication diagrams; `IsNoetherian` is the
canonical formulation of ACC on submodules.
-/
def GradedModuleHasACC
    {A : Type v} [CommRing A] (I : Ideal A) (N : ℕ → ModuleCat.{v} A)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (N n : Type v))) : Prop := by
  classical
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (N n : Type v)) := hN
  exact IsNoetherian (associatedGradedRing I)
    (DirectSum ℕ (fun n => (N n : Type v)))

/-! ## The inverse-limit filtration and topology -/

/-- The kernel filtration `F^n = Ker(M → H^p(X,F_n))` on an inverse limit. -/
def inverseSystemLimitFiltration
    {A : Type v} [CommRing A]
    {M : InverseSystem ℕ+ (ModuleCat.{v} A)} (n : ℕ+) :
    Submodule A ((InverseSystemLimit M : ModuleCat.{v} A) : Type v) :=
  LinearMap.ker ((limit.π M (op n)).hom)

/-- The degree-zero member `F^0=M` of the source's filtration. -/
abbrev inverseSystemLimitFiltrationZero
    {A : Type v} [CommRing A]
    {M : InverseSystem ℕ+ (ModuleCat.{v} A)} :
    Submodule A ((InverseSystemLimit M : ModuleCat.{v} A) : Type v) :=
  ⊤

/-- The source's filtration with `F^0=M` and positive stages thereafter. -/
def inverseSystemLimitFiltrationAt
    {A : Type v} [CommRing A]
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) (n : ℕ) :
    Submodule A ((InverseSystemLimit M : ModuleCat.{v} A) : Type v) :=
  if h : 0 < n then inverseSystemLimitFiltration (M := M) ⟨n, h⟩ else ⊤

/-- The limit topology induced by the discrete topologies on all stages. -/
@[instance_reducible]
def inverseSystemLimitTopology
    {A : Type v} [CommRing A]
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) :
    TopologicalSpace ((InverseSystemLimit M : ModuleCat.{v} A) : Type v) :=
  ⨅ n : ℕ+, TopologicalSpace.induced
    ((limit.π M (op n)).hom)
    (⊥ : TopologicalSpace (M.obj (op n) : Type v))

/-- The canonical `I`-adic topology on the inverse-limit module. -/
abbrev inverseSystemLimitIAdicTopology
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) :
    TopologicalSpace ((InverseSystemLimit M : ModuleCat.{v} A) : Type v) :=
  I.adicModuleTopology ((InverseSystemLimit M : ModuleCat.{v} A) : Type v)

/-- The uniform filtration estimate mentioned in the topology lemma's footnote. -/
def inverseSystemLimitHasUniformAdicBound
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ,
    inverseSystemLimitFiltrationAt M (n + c) ≤
      I ^ n • (⊤ : Submodule A
        ((InverseSystemLimit M : ModuleCat.{v} A) : Type v))

/-- The underlying inverse-limit module in the cohomology notation. -/
abbrev cohomologyLimit
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : ModuleCat.{v} A :=
  InverseSystemLimit (cohomologySystem H S p)

/-! ## 28.1. Inverse systems and cohomology, I -/

/-- `lemma-ML-general`: the first graded-ACC criterion for Mittag--Leffler. -/
theorem lemma_ML_general
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S (p + 1)) hN) :
    cohomologySystemIsMittagLeffler H S p := by
  sorry

/-- The uniform stable-image conclusion recorded in the first footnote. -/
theorem lemma_ML_general_stable_image
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S (p + 1)) hN) :
    cohomologySystemHasUniformStableImage H S p := by
  sorry

/-- `lemma-ML-general-better`: the criterion using the stable `N_n`. -/
theorem lemma_ML_general_better
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S (p + 1)) hN) :
    cohomologySystemIsMittagLeffler H S p := by
  sorry

/-- The uniform stable-image conclusion recorded in the second footnote. -/
theorem lemma_ML_general_better_stable_image
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S (p + 1)) hN) :
    cohomologySystemHasUniformStableImage H S p := by
  sorry

/--
`lemma-topology-I-adic-general`: the ordinary graded-ACC topology result.
The source proof chooses generators of `I`, so finite generation is explicit
in this interface.
-/
theorem lemma_topology_I_adic_general
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S p n : Type v)))
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitTopology (cohomologySystem H S p) =
      inverseSystemLimitIAdicTopology I (cohomologySystem H S p) := by
  sorry

/-- The uniform filtration estimate recorded in the topology lemma's footnote. -/
theorem lemma_topology_I_adic_general_uniform_bound
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S p n : Type v)))
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitHasUniformAdicBound I (cohomologySystem H S p) := by
  sorry

/-- `lemma-topology-I-adic-general-better`: the stable-`N_n` topology result. -/
theorem lemma_topology_I_adic_general_better
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S p n : Type v)))
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitTopology (cohomologySystem H S p) =
      inverseSystemLimitIAdicTopology I (cohomologySystem H S p) := by
  sorry

/-- The same uniform filtration estimate for the stable-`N_n` criterion. -/
theorem lemma_topology_I_adic_general_better_uniform_bound
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S p n : Type v)))
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitHasUniformAdicBound I (cohomologySystem H S p) := by
  sorry

end

end Formalization.Books.Cohomology.Unit28
