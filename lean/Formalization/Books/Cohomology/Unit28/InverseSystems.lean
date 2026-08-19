import Formalization.Books.Algebra.Unit86.MittagLefflerSystems
import Formalization.Books.Categories.Unit21.LimitsAndColimitsOverPreorderedSets
import Formalization.Books.Cohomology.Unit02.CohomologyOfSheaves
import Formalization.Books.Homology.Unit12.CohomologicalDeltaFunctors
import Formalization.Books.MoreAlgebra.Unit04.CommentOnArtinRees
import Formalization.Books.MoreAlgebra.Unit36.OpenMapping
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

/-! ## Graded compatibility needed by the source arguments -/

/-- The degree-`p` family `H^p(X,I^n F_{n+1})`. -/
abbrev powerCohomologyModuleFamily
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : ℕ → ModuleCat.{v} A :=
  fun n => (H.functor p).obj (S.power n n le_rfl)

/- The boundary map at the matching stage has the target used by the
   degree-indexed power cohomology family. -/
def cohomologyBoundaryAtStage
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (n : ℕ+) (p : ℕ) :
    (cohomologySystem H S p).obj (op n) ⟶
      powerCohomologyModuleFamily H S (p + 1) (n : ℕ) :=
  cohomologyBoundary H S n (n : ℕ) le_rfl p

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

/- A graded action on a family of submodules must be the restriction of the
   action on its ambient family.  An unrelated `DirectSum.Gmodule` instance
   is not enough for the graded-submodule arguments in the source proofs. -/
def GradedSubmoduleActionCompatible
    {A : Type v} [CommRing A] (I : Ideal A)
    (P : ℕ → ModuleCat.{v} A)
    (N : ∀ n, Submodule A ((P n : Type v)))
    (hP : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v)))
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (N n : Type v))) : Prop := by
  classical
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP
  letI : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP.toGdistribMulAction.toGMulAction.toGSMul
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (N n : Type v)) := hN
  letI : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => (N n : Type v)) := hN.toGdistribMulAction.toGMulAction.toGSMul
  exact ∀ (k n : ℕ) (a : associatedGradedRingPiece I k) (x : N n),
    ((@GradedMonoid.GSMul.smul ℕ ℕ (fun n => associatedGradedRingPiece I n)
      (fun n => (N n : Type v)) _ _ k n a x : N (k + n)) : P (k + n)) =
      @GradedMonoid.GSMul.smul ℕ ℕ (fun n => associatedGradedRingPiece I n)
        (fun n => (P n : Type v)) _ _ k n a (x : P n)

/- The direct sum of the component images of the boundary maps must be a
   graded submodule of the ambient power-cohomology family. -/
def GradedBoundaryImageCompatible
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A))
    (P : ℕ → ModuleCat.{v} A)
    (δ : ∀ n : ℕ+, M.obj (op n) ⟶ P (n : ℕ))
    (hP : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v))) : Prop := by
  classical
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP
  letI : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP.toGdistribMulAction.toGMulAction.toGSMul
  exact ∀ (k : ℕ) (n : ℕ+) (a : associatedGradedRingPiece I k)
    (x : P (n : ℕ)),
    x ∈ LinearMap.range (δ n).hom →
      (@GradedMonoid.GSMul.smul ℕ ℕ (fun n => associatedGradedRingPiece I n)
        (fun n => (P n : Type v)) _ _ k (n : ℕ) a x) ∈ LinearMap.range
        (δ ⟨k + (n : ℕ), Nat.add_pos_right k n.2⟩).hom

/- The target-side closure condition above is not enough to run the source
   argument: the correction terms live in the ML system itself.  This
   predicate records the missing graded action, its compatibility with the
   connecting maps, and the fact that sufficiently high-degree corrections
   disappear after passing to a lower stage. -/
def GradedBoundaryActionCompatible
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A))
    (P : ℕ → ModuleCat.{v} A)
    (δ : ∀ n : ℕ+, M.obj (op n) ⟶ P (n : ℕ))
    (hP : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v))) : Prop := by
  classical
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP
  letI : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => (P n : Type v)) := hP.toGdistribMulAction.toGMulAction.toGSMul
  exact ∃ action : ∀ (k : ℕ) (n : ℕ+),
      associatedGradedRingPiece I k →
        (M.obj (op n) : Type v) →
          (M.obj (op ⟨k + (n : ℕ), Nat.add_pos_right k n.2⟩) : Type v),
    (∀ (k : ℕ) (n : ℕ+) (a : associatedGradedRingPiece I k)
      (x : (M.obj (op n) : Type v)),
      (δ ⟨k + (n : ℕ), Nat.add_pos_right k n.2⟩).hom
          (action k n a x) =
        @GradedMonoid.GSMul.smul ℕ ℕ
          (fun n => associatedGradedRingPiece I n)
          (fun n => (P n : Type v)) _ _ k (n : ℕ) a ((δ n).hom x)) ∧
    (∀ (k : ℕ) (n l : ℕ+) (h : l ≤
      ⟨k + (n : ℕ), Nat.add_pos_right k n.2⟩)
      (hk : (l : ℕ) ≤ k) (a : associatedGradedRingPiece I k)
      (x : (M.obj (op n) : Type v)),
      (M.map (opHomOfLE h)).hom (action k n a x) = 0)

/- The naturality argument in the source puts each boundary image in every
   component used to define the stable intersection.  The abstract sheaf
   data above does not itself expose the required morphism of short exact
   sequences, so this fact is kept as an explicit reusable interface. -/
def BoundaryMapsIntoStablePowerCohomology
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) : Prop :=
  ∀ (n : ℕ+)
    (x : ((cohomologySystem H S p).obj (op n) : Type v)),
    (cohomologyBoundaryAtStage H S n p).hom x ∈
      stablePowerCohomologySubmodule H S (p + 1) (n : ℕ)

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

/- The image of the `n`th filtration piece in the next cohomology stage. -/
def inverseSystemLimitFiltrationImage
    {A : Type v} [CommRing A]
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) (n : ℕ) :
    Submodule A ((M.obj (op (positiveStage n)) : Type v)) :=
  LinearMap.range (((limit.π M (op (positiveStage n))).hom.comp
    (inverseSystemLimitFiltrationAt M n).subtype))

/- The submodule called `E_n` in the topology proof. -/
def powerCohomologyFiltrationSubmodule
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p n : ℕ) :
    Submodule A ((powerCohomologyModuleFamily H S p n : Type v)) :=
  (inverseSystemLimitFiltrationImage (cohomologySystem H S p) n).comap
    (((H.functor p).map (S.powerToStage n n le_rfl)).hom)

/- The corresponding `E_n` after restricting to the stable `N_n`. -/
def stablePowerCohomologyFiltrationSubmodule
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p n : ℕ) :
    Submodule A ((stablePowerCohomologyModuleFamily H S p n : Type v)) :=
  (powerCohomologyFiltrationSubmodule H S p n).comap
    (stablePowerCohomologySubmodule H S p n).subtype

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

/- The first comparison in the source's topology proof is the inclusion
   `I F^n ⊆ F^(n+1)`.  It is not a consequence of an arbitrary inverse system
   of modules, so expose it as the filtration compatibility needed by the
   abstract topology criteria. -/
def inverseSystemLimitFiltrationIsIAdicallyCompatible
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A)) : Prop :=
  ∀ n : ℕ, I • inverseSystemLimitFiltrationAt M n ≤
    inverseSystemLimitFiltrationAt M (n + 1)

/- The topology proof also uses the graded action induced on the associated
   graded filtration.  This interface makes both links explicit: the
   filtration pieces receive a graded action, and the power-cohomology
   filtration maps onto them as a graded map.  The final clause identifies
   homogeneous action with the underlying ideal scalar action. -/
def FiltrationGradedActionCompatible
    {A : Type v} [CommRing A] (I : Ideal A)
    (M : InverseSystem ℕ+ (ModuleCat.{v} A))
    (P : ℕ → ModuleCat.{v} A)
    (E : ∀ n, Submodule A ((P n : Type v)))
    (hE : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (E n : Type v))) : Prop := by
  classical
  letI : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (E n : Type v)) := hE
  letI : GradedMonoid.GSMul (associatedGradedRingPiece I)
      (fun n => (E n : Type v)) := hE.toGdistribMulAction.toGMulAction.toGSMul
  exact ∃ hF : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (submoduleQuotient (inverseSystemLimitFiltrationAt M n)
          (inverseSystemLimitFiltrationAt M (n + 1)) : Type v)),
    ∃ e : ∀ n, (E n : Type v) →ₗ[A]
        submoduleQuotient (inverseSystemLimitFiltrationAt M n)
          (inverseSystemLimitFiltrationAt M (n + 1)),
      (∀ n, Function.Surjective (e n)) ∧
      (letI : DirectSum.Gmodule (associatedGradedRingPiece I)
          (fun n =>
            (submoduleQuotient (inverseSystemLimitFiltrationAt M n)
              (inverseSystemLimitFiltrationAt M (n + 1)) : Type v)) := hF
       ∀ (k n : ℕ) (a : associatedGradedRingPiece I k)
         (x : (E n : Type v)),
         e (k + n)
             (@GradedMonoid.GSMul.smul ℕ ℕ
               (fun n => associatedGradedRingPiece I n)
               (fun n => (E n : Type v)) _ _ k n a x) =
           @GradedMonoid.GSMul.smul ℕ ℕ
             (fun n => associatedGradedRingPiece I n)
             (fun n =>
               (submoduleQuotient (inverseSystemLimitFiltrationAt M n)
                 (inverseSystemLimitFiltrationAt M (n + 1)) : Type v)) _ _ k n a
             (e n x)) ∧
      (letI : DirectSum.Gmodule (associatedGradedRingPiece I)
          (fun n =>
            (submoduleQuotient (inverseSystemLimitFiltrationAt M n)
              (inverseSystemLimitFiltrationAt M (n + 1)) : Type v)) := hF
       ∀ (k n : ℕ) (r : (I ^ k : Submodule A A))
         (x : (inverseSystemLimitFiltrationAt M n : Type v)),
         ∃ y : (inverseSystemLimitFiltrationAt M (k + n) : Type v),
           @GradedMonoid.GSMul.smul ℕ ℕ
               (fun n => associatedGradedRingPiece I n)
               (fun n =>
                 (submoduleQuotient (inverseSystemLimitFiltrationAt M n)
                   (inverseSystemLimitFiltrationAt M (n + 1)) : Type v)) _ _ k n
               (Submodule.Quotient.mk r) (Submodule.Quotient.mk x) =
             Submodule.Quotient.mk y ∧
           (y : ((inverseSystemLimitFiltrationAt M (k + n) : Type v))) =
             (r : A) • (x : ((InverseSystemLimit M : ModuleCat.{v} A) : Type v)))

/-! ## 28.1. Inverse systems and cohomology, I -/

/-- `lemma-ML-general`: the first graded-ACC criterion for Mittag--Leffler. -/
theorem lemma_ML_general
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hBoundary : GradedBoundaryImageCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hN)
    (hAction : GradedBoundaryActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hN)
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
    (hBoundary : GradedBoundaryImageCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hN)
    (hAction : GradedBoundaryActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hN)
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
    (hP : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (powerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hStableCompatible : GradedSubmoduleActionCompatible I
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => stablePowerCohomologySubmodule H S (p + 1) n) hP hN)
    (hBoundary : GradedBoundaryImageCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hP)
    (hAction : GradedBoundaryActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hP)
    (hBoundaryStable : BoundaryMapsIntoStablePowerCohomology H S p)
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
    (hP : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (powerCohomologyModuleFamily H S (p + 1) n : Type v)))
    (hStableCompatible : GradedSubmoduleActionCompatible I
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => stablePowerCohomologySubmodule H S (p + 1) n) hP hN)
    (hBoundary : GradedBoundaryImageCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hP)
    (hAction : GradedBoundaryActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S (p + 1))
      (fun n => cohomologyBoundaryAtStage H S n p) hP)
    (hBoundaryStable : BoundaryMapsIntoStablePowerCohomology H S p)
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S (p + 1)) hN) :
    cohomologySystemHasUniformStableImage H S p := by
  sorry

/--
`lemma-topology-I-adic-general`: the ordinary graded-ACC topology result.
The source proof chooses generators of `I`, so finite generation is explicit
in this interface.

Proof roadmap:
* No hypothesis is missing.  Factor the common hard part of this theorem and
  `lemma_topology_I_adic_general_uniform_bound` into a private theorem, placed
  before both wrappers, named
  `inverseSystemLimitHasUniformAdicBound_of_gradedACC`.  It should be universe
  polymorphic in `A : Type v`, take
  `M : InverseSystem ℕ+ (ModuleCat.{v} A)`, `P : ℕ → ModuleCat.{v} A`, and
  `E : ∀ n, Submodule A (P n)`, followed by the seven inputs represented
  here by `hI`, `hN`, `hE`, `hECompatible`, `hFiltration`,
  `hFiltrationGraded`, and `hACC`, and conclude
  `inverseSystemLimitHasUniformAdicBound I M`.  The detailed construction is
  recorded at the uniform-bound wrapper below.
* Apply that helper with `M := cohomologySystem H S p`,
  `P := powerCohomologyModuleFamily H S p`, and
  `E := fun n => powerCohomologyFiltrationSubmodule H S p n`; call the result
  `hbound`.
* Prove `hpow : ∀ n, I ^ n • (⊤ : Submodule A (cohomologyLimit H S p)) ≤
  inverseSystemLimitFiltrationAt (cohomologySystem H S p) n` by induction.
  The successor step is `smul_mono_right I` applied to the induction
  hypothesis, followed by `hFiltration n`; normalize with `pow_succ'`,
  `mul_smul`, and `Nat.add_comm`.
* Establish the translated-kernel basis
  `∀ x, (@nhds _ (inverseSystemLimitTopology (cohomologySystem H S p)) x).HasBasis
    (fun _ : ℕ => True)
    (fun n => (fun y => x + y) ''
      (inverseSystemLimitFiltrationAt (cohomologySystem H S p) n : Set _))`.
  At zero, unfold `inverseSystemLimitTopology`, rewrite with `nhds_iInf`,
  `nhds_induced`, `nhds_discrete`, and `Filter.comap_pure`, and collapse finite
  intersections of kernels using `Filter.hasBasis_iInf_principal` plus
  `limit.w`; the proof of
  `Formalization.Books.MoreAlgebra.Unit36.inverseLimit_kernels_form_fundamental_system`
  in `MoreAlgebra/Unit36/TopologicalGroups.lean` is the exact model.  Translate
  from zero with `map_add_left_nhds_zero`.
* Finish with
  `Formalization.Books.MoreAlgebra.Unit36.topologicalSpace_eq_iAdicModuleTopology_of_cofinal_basis`
  from `MoreAlgebra/Unit36/TopologicalRings.lean`, instantiated with
  `R := A`, `M := (cohomologyLimit H S p : Type v)`,
  `t := inverseSystemLimitTopology (cohomologySystem H S p)`, and
  `K := inverseSystemLimitFiltrationAt (cohomologySystem H S p)`, supplying
  the basis, `hpow`, and `hbound` in that order.
-/
theorem lemma_topology_I_adic_general
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S p n : Type v)))
    (hE : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (powerCohomologyFiltrationSubmodule H S p n : Type v)))
    (hECompatible : GradedSubmoduleActionCompatible I
      (powerCohomologyModuleFamily H S p)
      (fun n => powerCohomologyFiltrationSubmodule H S p n) hN hE)
    (hFiltration : inverseSystemLimitFiltrationIsIAdicallyCompatible I
      (cohomologySystem H S p))
    (hFiltrationGraded : FiltrationGradedActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S p)
      (fun n => powerCohomologyFiltrationSubmodule H S p n) hE)
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitTopology (cohomologySystem H S p) =
      inverseSystemLimitIAdicTopology I (cohomologySystem H S p) := by
  sorry

/-- The uniform filtration estimate recorded in the topology lemma's footnote.

Proof roadmap for the shared graded-ACC-to-uniform-bound bridge:
* Put `G := associatedGradedRing I`, `F n :=
  inverseSystemLimitFiltrationAt (cohomologySystem H S p) n`, and
  `Q n := submoduleQuotient (F n) (F (n + 1))`.  Unpack
  `hFiltrationGraded` as `⟨hQ, e, he_surj, he_graded, hsmul⟩`, installing its
  `DirectSum.Gmodule` instances with `letI`.  Use `hECompatible` to make the
  componentwise inclusions `E n → P n` into a `G`-linear map
  `iE : DirectSum ℕ (fun n => (E n : Type v)) →ₗ[G]
    DirectSum ℕ (fun n => (P n : Type v))`.  Its `toFun` is
  `DirectSum.map (fun n => (E n).subtype.toAddMonoidHom)`; prove `map_smul'`
  by `DirectSum.induction_on` twice, reducing the homogeneous case with
  `DirectSum.Gmodule.of_smul_of`, `DirectSum.map_of`, and `hECompatible`.
  The same construction applied to `e` and `he_graded` gives a `G`-linear
  `qE : DirectSum ℕ (fun n => (E n : Type v)) →ₗ[G]
    DirectSum ℕ (fun n => (Q n : Type v))`.
* Prove `iE` injective componentwise, turn `hACC` into a local
  `IsNoetherian G (DirectSum ℕ (fun n => (P n : Type v)))` instance, and use
  `isNoetherian_of_injective iE`.  Prove `qE` surjective with
  `DirectSum.lmap_surjective.mpr he_surj` (its underlying function is the
  componentwise `DirectSum.lmap e`) and use `isNoetherian_of_surjective`.
  Thus `IsNoetherian.noetherian (⊤ : Submodule G (DirectSum ℕ Q))` supplies a
  finite generating family via
  `Submodule.fg_iff_exists_fin_generating_family`.
* Homogenize that family: replace every generator by its finitely many
  components and use `DirectSum.sum_support_of` to show the replacement still
  spans.  Let `c` be the maximum of their degrees.  Choose representatives
  `a_j : F (degree j)` of the homogeneous quotient generators using
  `Submodule.mkQ_surjective`.
* For every `m ≥ c`, prove the key equality
  `F (m + 1) = F (m + 2) ⊔ I • F m`.  Project a homogeneous spanning
  expression to degree `m + 1`; `DirectSum.Gmodule.of_smul_of` eliminates all
  degree-mismatched terms.  Quotient-induct the remaining scalars and rewrite
  their products using
  `Formalization.Books.Algebra.Unit150.associatedGradedPieceMul_mk_mk` from
  `Algebra/Unit150/FormallyEtaleMaps.lean`.  Factor
  `I ^ (m + 1 - degree j)` as `I * I ^ (m - degree j)` using
  `Ideal.IsTwoSided.pow_add`; the last clause `hsmul` then identifies the
  homogeneous action with the actual scalar multiple of `a_j`.  The opposite
  inclusion uses the structural antitonicity of the kernel filtration and
  `hFiltration`.
* Iterating the key equality shows `I • F m` is dense in `F (m + 1)` for the
  kernel topology.  Use `hI` to choose a finite generating family of `I` and
  form the continuous additive homomorphism
  `u : (Fin r → (F m : Type v)) →+ (F (m + 1) : Type v)` sending
  `(x_i)` to `∑ i, k_i • x_i`.  Apply
  `Formalization.Books.MoreAlgebra.Unit36.openMapping_or_nowhereDense_image`
  from `MoreAlgebra/Unit36/OpenMapping.lean`.  Supply completeness, linearity,
  and the countable kernel basis by adapting, respectively,
  `inverseLimit_is_complete`, `inverseLimit_is_linearly_topologized`, and
  `inverseLimit_kernels_form_fundamental_system` from
  `MoreAlgebra/Unit36/TopologicalGroups.lean` to this module-valued inverse
  limit and its closed filtration submodules.  The density statement excludes
  the nowhere-dense alternative for every basic open subgroup, so `u` is open;
  its dense image is therefore all of `F (m + 1)`.  Conclude
  `I • F m = F (m + 1)` for `m ≥ c`.
* Package `F` as `Ideal.Filtration I (cohomologyLimit H S p)`: prove `mono`
  from `limit.w` (split the zero index) and use `hFiltration` for `smul_le`.
  The preceding equality is its `Ideal.Filtration.Stable` witness.  Apply
  `Ideal.Filtration.Stable.exists_pow_smul_eq` from
  `Mathlib/RingTheory/Filtration.lean` and obtain
  `F (c + n) = I ^ n • F c ≤ I ^ n • ⊤`; commute `c + n` to `n + c` to
  assemble `inverseSystemLimitHasUniformAdicBound`.

Do not retry `Ideal.Filtration.submodule_fg_iff_stable`: it asks for finite
generation of every `F n` and of the Rees-filtration submodule, neither of
which follows from the supplied graded ACC.  The open-mapping step above is
what upgrades density to the required equality.
-/
theorem lemma_topology_I_adic_general_uniform_bound
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n => (powerCohomologyModuleFamily H S p n : Type v)))
    (hE : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (powerCohomologyFiltrationSubmodule H S p n : Type v)))
    (hECompatible : GradedSubmoduleActionCompatible I
      (powerCohomologyModuleFamily H S p)
      (fun n => powerCohomologyFiltrationSubmodule H S p n) hN hE)
    (hFiltration : inverseSystemLimitFiltrationIsIAdicallyCompatible I
      (cohomologySystem H S p))
    (hFiltrationGraded : FiltrationGradedActionCompatible I
      (cohomologySystem H S p)
      (powerCohomologyModuleFamily H S p)
      (fun n => powerCohomologyFiltrationSubmodule H S p n) hE)
    (hACC : GradedModuleHasACC I
      (powerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitHasUniformAdicBound I (cohomologySystem H S p) := by
  sorry

/-- `lemma-topology-I-adic-general-better`: the stable-`N_n` topology result.

Proof roadmap:
* No extra hypothesis is needed.  Invoke the common private bridge described
  at `lemma_topology_I_adic_general_uniform_bound` with
  `M := cohomologySystem H S p`,
  `P := stablePowerCohomologyModuleFamily H S p`, and
  `E := fun n => stablePowerCohomologyFiltrationSubmodule H S p n`.  The
  arguments `hN`, `hE`, `hECompatible`, `hFiltration`,
  `hFiltrationGraded`, and `hACC` have exactly the bridge's types; no
  comparison with the non-stable power family is required.
* Reuse the kernel-basis and power-inclusion constructions from
  `lemma_topology_I_adic_general`: they depend only on
  `cohomologySystem H S p` and `hFiltration`, not on the chosen ambient graded
  family.
* Apply
  `Formalization.Books.MoreAlgebra.Unit36.topologicalSpace_eq_iAdicModuleTopology_of_cofinal_basis`
  with `R := A`, `M := (cohomologyLimit H S p : Type v)`, and
  `K := inverseSystemLimitFiltrationAt (cohomologySystem H S p)`, using the
  stable-family bridge result as its uniform bound.
-/
theorem lemma_topology_I_adic_general_better
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S p n : Type v)))
    (hE : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyFiltrationSubmodule H S p n : Type v)))
    (hECompatible : GradedSubmoduleActionCompatible I
      (stablePowerCohomologyModuleFamily H S p)
      (fun n => stablePowerCohomologyFiltrationSubmodule H S p n) hN hE)
    (hFiltration : inverseSystemLimitFiltrationIsIAdicallyCompatible I
      (cohomologySystem H S p))
    (hFiltrationGraded : FiltrationGradedActionCompatible I
      (cohomologySystem H S p)
      (stablePowerCohomologyModuleFamily H S p)
      (fun n => stablePowerCohomologyFiltrationSubmodule H S p n) hE)
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitTopology (cohomologySystem H S p) =
      inverseSystemLimitIAdicTopology I (cohomologySystem H S p) := by
  sorry

/-- The same uniform filtration estimate for the stable-`N_n` criterion.

Proof roadmap:
* Apply the shared
  `inverseSystemLimitHasUniformAdicBound_of_gradedACC` construction detailed at
  `lemma_topology_I_adic_general_uniform_bound`, now with
  `P := stablePowerCohomologyModuleFamily H S p` and
  `E := fun n => stablePowerCohomologyFiltrationSubmodule H S p n`.
* In the two direct-sum maps, install the supplied stable-family structures
  `hN` and `hE`; use `hECompatible` for the inclusion into `P` and unpack
  `hFiltrationGraded` for the surjection onto
  `DirectSum ℕ (fun n => submoduleQuotient
    (inverseSystemLimitFiltrationAt (cohomologySystem H S p) n)
    (inverseSystemLimitFiltrationAt (cohomologySystem H S p) (n + 1)))`.
  All remaining kernel-filtration, density, open-mapping, and stability steps
  are definitionally the ordinary roadmap after these substitutions.
* Return the bridge conclusion directly; the topology comparison theorem is
  not needed in this wrapper.  In particular, do not try to reduce this to
  the ordinary uniform-bound theorem: there is no map from the stable graded
  family to the ordinary one in the hypotheses.
-/
theorem lemma_topology_I_adic_general_better_uniform_bound
    {A : Type v} [CommRing A] {X : TopCat.{v}} {I : Ideal A}
    (H : SheafCohomologicalDeltaFunctor A X)
    (S : IAdicSheafSystem A X I) (p : ℕ) (hI : I.FG)
    (hN : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyModuleFamily H S p n : Type v)))
    (hE : DirectSum.Gmodule (associatedGradedRingPiece I)
      (fun n =>
        (stablePowerCohomologyFiltrationSubmodule H S p n : Type v)))
    (hECompatible : GradedSubmoduleActionCompatible I
      (stablePowerCohomologyModuleFamily H S p)
      (fun n => stablePowerCohomologyFiltrationSubmodule H S p n) hN hE)
    (hFiltration : inverseSystemLimitFiltrationIsIAdicallyCompatible I
      (cohomologySystem H S p))
    (hFiltrationGraded : FiltrationGradedActionCompatible I
      (cohomologySystem H S p)
      (stablePowerCohomologyModuleFamily H S p)
      (fun n => stablePowerCohomologyFiltrationSubmodule H S p n) hE)
    (hACC : GradedModuleHasACC I
      (stablePowerCohomologyModuleFamily H S p) hN) :
    inverseSystemLimitHasUniformAdicBound I (cohomologySystem H S p) := by
  sorry

end

end Formalization.Books.Cohomology.Unit28
