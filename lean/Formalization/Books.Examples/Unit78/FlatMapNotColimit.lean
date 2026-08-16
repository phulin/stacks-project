import Formalization.«Books.MoreMorphisms».Unit19.Normalization
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Examples, Chapter 78: flat maps are not directed limits of finitely presented flat maps

This chapter records the absolute-integral-closure example and the obstruction used
to rule out a filtered colimit presentation.  The standard algebraic constructions
come from Mathlib.  The strict henselization, abelian-surface, and étale/local-
cohomology parts are exposed as source-facing structures because those particular
geometric constructions are not available in the imported Mathlib API.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace Formalization.«Books.Examples».Unit78

universe u v

/- The earlier MoreMorphisms file that exposes these two properties is not
   syntactically consumable by the attached Lean environment, so the exact
   universal-property interfaces are repeated locally rather than importing a
   malformed dependency. -/
def IsHenselization
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) : Prop :=
  IsLocalHom f ∧
    ∀ (C : Type u) [CommRing C] [HenselianLocalRing C],
      ∀ (g : A →+* C), IsLocalHom g →
        ∃! h : B →+* C, IsLocalHom h ∧ h.comp f = g

def IsStrictHenselization
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing B ∧ IsSepClosed (IsLocalRing.ResidueField B) ∧
    ∀ (C : Type u) [CommRing C] [HenselianLocalRing C]
      [IsSepClosed (IsLocalRing.ResidueField C)],
      ∀ (g : A →+* C), IsLocalHom g →
        ∃! h : B →+* C, IsLocalHom h ∧ h.comp f = g

/-! ## The polynomial ring and its absolute integral closure -/

/- The source writes `F_p[x₁, ..., xₙ]`; Mathlib's canonical finite-variable
   polynomial ring is `MvPolynomial (Fin n) (ZMod p)`. -/
abbrev polynomialRing (p n : ℕ) [Fact p.Prime] :=
  MvPolynomial (Fin n) (ZMod p)

/-- Evaluation at the origin of affine `n`-space over `F_p`. -/
def polynomialOriginEvaluation (p n : ℕ) [Fact p.Prime] :
    polynomialRing p n →+* ZMod p :=
  MvPolynomial.eval₂Hom (RingHom.id _) (fun _ => 0)

/-- The maximal ideal of the origin in the polynomial ring. -/
def polynomialOriginIdeal (p n : ℕ) [Fact p.Prime] : Ideal (polynomialRing p n) :=
  RingHom.ker (polynomialOriginEvaluation p n)

theorem polynomialOriginIdeal_isMaximal (p n : ℕ) [Fact p.Prime] :
    (polynomialOriginIdeal p n).IsMaximal := by
  sorry

theorem polynomialOriginIdeal_isPrime (p n : ℕ) [Fact p.Prime] :
    (polynomialOriginIdeal p n).IsPrime := by
  exact (polynomialOriginIdeal_isMaximal p n).isPrime

/-- The origin of `Spec(F_p[x₁, ..., xₙ])`. -/
abbrev polynomialOriginScheme (p n : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (polynomialRing p n))

noncomputable def polynomialOriginPoint (p n : ℕ) [Fact p.Prime] :
    polynomialOriginScheme p n :=
  ⟨polynomialOriginIdeal p n, polynomialOriginIdeal_isPrime p n⟩

theorem polynomialOriginPoint_asIdeal (p n : ℕ) [Fact p.Prime] :
    (polynomialOriginPoint p n).asIdeal = polynomialOriginIdeal p n := by
  sorry

/- A ring map is used explicitly here so the chosen embedding into the algebraic
   closure of the fraction field is not confused with an unrelated algebra
   structure. -/
noncomputable def absoluteIntegralClosureEmbedding (A : Type u) [CommRing A]
    [IsDomain A] : A →+* AlgebraicClosure (FractionRing A) :=
  (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).comp
    (algebraMap A (FractionRing A))

noncomputable def integralClosureAlong {A K : Type u} [CommRing A] [CommRing K]
    (ι : A →+* K) :
    letI : Algebra A K := ι.toAlgebra
    Subalgebra A K :=
  letI : Algebra A K := ι.toAlgebra
  integralClosure A K

/- The subtype of `integralClosureAlong` is the actual ring used for `A⁺`. -/
noncomputable def absoluteIntegralClosureSubalgebra (A : Type u) [CommRing A]
    [IsDomain A] :
    letI : Algebra A (AlgebraicClosure (FractionRing A)) :=
      (absoluteIntegralClosureEmbedding A).toAlgebra
    Subalgebra A (AlgebraicClosure (FractionRing A)) :=
  integralClosureAlong (absoluteIntegralClosureEmbedding A)

/-- The absolute integral closure of a domain in an algebraic closure of its fraction field. -/
abbrev absoluteIntegralClosure (A : Type u) [CommRing A] [IsDomain A] :=
  absoluteIntegralClosureSubalgebra A

/-- The canonical map from a domain to its absolute integral closure. -/
noncomputable def absoluteIntegralClosureMap (A : Type u) [CommRing A] [IsDomain A] :
    A →+* absoluteIntegralClosure A :=
  algebraMap A (absoluteIntegralClosure A)

/-- A source-facing characterization of an absolute integral closure. -/
structure AbsoluteIntegralClosureWitness (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) where
  fractionField : Type u
  [fractionFieldField : Field fractionField]
  [algebraA : Algebra A fractionField]
  [algebraB : Algebra B fractionField]
  algebraicallyClosed : IsAlgClosed fractionField
  isIntegralClosure : IsIntegralClosure B A fractionField
  algebraMap_compatibility :
    (algebraMap B fractionField).comp f = algebraMap A fractionField

def IsAbsoluteIntegralClosureOf (A B : Type u) [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Nonempty (AbsoluteIntegralClosureWitness A B f)

theorem absoluteIntegralClosure_isAbsoluteIntegralClosure (A : Type u) [CommRing A]
    [IsDomain A] :
    IsAbsoluteIntegralClosureOf A (absoluteIntegralClosure A)
      (absoluteIntegralClosureMap A) := by
  sorry

/-- Gabber's flatness theorem for the absolute integral closure in characteristic `p`. -/
theorem polynomialAbsoluteIntegralClosure_flat (p n : ℕ) [Fact p.Prime] :
    RingHom.Flat (absoluteIntegralClosureMap (polynomialRing p n)) := by
  sorry

/-! ## Filtered colimits of finitely presented flat algebras -/

/- The categorical object `Under (CommRingCat.of A)` is the canonical category of
   `A`-algebras. -/
noncomputable def algebraAsUnder {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom f)

structure FilteredFinitelyPresentedFlatColimit {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) where
  index : Type u
  [indexCategory : Category.{u} index]
  [indexFiltered : IsFiltered index]
  diagram : index ⥤ Under (CommRingCat.of A)
  cocone : Cocone diagram
  isColimit : IsColimit cocone
  targetIso : cocone.pt ≅ algebraAsUnder f
  finitelyPresented : ∀ i, RingHom.FinitePresentation (diagram.obj i).hom.hom
  flat : ∀ i, RingHom.Flat (diagram.obj i).hom.hom

/-- The source's phrase “filtered colimit of finitely presented flat `A`-algebras”. -/
def IsFilteredColimitOfFinitelyPresentedFlat {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  Nonempty (FilteredFinitelyPresentedFlatColimit f)

/-- The three-variable absolute-integral-closure counterexample. -/
theorem polynomialAbsoluteIntegralClosure_not_filteredColimit_three (p : ℕ)
    [Fact p.Prime] :
    ¬ IsFilteredColimitOfFinitelyPresentedFlat
      (absoluteIntegralClosureMap (polynomialRing p 3)) := by
  sorry

/-- The source's claim for polynomial rings in at least three variables. -/
theorem polynomialAbsoluteIntegralClosure_not_filteredColimit_of_dimension_ge_three
    (p n : ℕ) [Fact p.Prime] (hn : 3 ≤ n) :
    ¬ IsFilteredColimitOfFinitelyPresentedFlat
      (absoluteIntegralClosureMap (polynomialRing p n)) := by
  sorry

/- The map from a stage to the specified target, obtained from the cocone and
   the target identification. -/
noncomputable def filteredColimitStageMap {A B : Type u} [CommRing A] [CommRing B]
    {f : A →+* B} (D : FilteredFinitelyPresentedFlatColimit f) (i : D.index) :
    letI : Category D.index := D.indexCategory
    (D.diagram.obj i).right →+* B :=
  letI : Category D.index := D.indexCategory
  ((D.cocone.ι.app i ≫ D.targetIso.hom).right).hom

/-- A map out of `S` factors through a stage of a filtered colimit. -/
def FactorsThroughFilteredStage {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    {f : A →+* B} (D : FilteredFinitelyPresentedFlatColimit f)
    (rToS : A →+* S) (sToB : S →+* B) : Prop :=
  letI : Category D.index := D.indexCategory
  ∃ i, ∃ g : S →+* (D.diagram.obj i).right,
    g.comp rToS = (D.diagram.obj i).hom.hom ∧
      (filteredColimitStageMap D i).comp g = sToB

/- A finite flat stage supplied by the slicing argument. -/
structure FiniteFlatFactor {R S : Type u} [CommRing R] [CommRing S]
    (rToS : R →+* S) where
  target : Type u
  [targetCommRing : CommRing target]
  rToTarget : R →+* target
  sToTarget : S →+* target
  compatibility : sToTarget.comp rToS = rToTarget
  finite : RingHom.Finite rToTarget
  flat : RingHom.Flat rToTarget

/- Finite flat modules over the henselian local base are free; this is the
   module-theoretic parenthetical used in the source's contradiction. -/
theorem finite_flat_module_free_over_local
    {R M : Type u} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.Free R M :=
  Module.free_of_flat_of_isLocalRing

structure FiniteFlatFactorOver {R S P : Type u} [CommRing R] [CommRing S] [CommRing P]
    (rToS : R →+* S) (sToP : S →+* P) where
  target : Type u
  [targetCommRing : CommRing target]
  rToTarget : R →+* target
  sToTarget : S →+* target
  compatibility : sToTarget.comp rToS = rToTarget
  finite : RingHom.Finite rToTarget
  flat : RingHom.Flat rToTarget
  targetToP : target →+* P
  targetToP_comp : targetToP.comp sToTarget = sToP

/-- The first assertion in the source's two-step obstruction. -/
def SlicingAssertion {R S : Type u} [CommRing R] [CommRing S]
    (rToS : R →+* S) : Prop :=
  ∀ (P : Type u) [CommRing P] (rToP : R →+* P),
    RingHom.Flat rToP → RingHom.FiniteType rToP →
      ∀ (sToP : S →+* P), sToP.comp rToS = rToP →
        ∃ F : FiniteFlatFactorOver rToS sToP,
          F.targetToP.comp F.rToTarget = rToP

/-- More Morphisms' henselian slicing lemma, in the form used by the source. -/
theorem henselian_slicing_assertion
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    (rToS : R →+* S) : SlicingAssertion rToS := by
  sorry

/-- The second assertion in the source's two-step obstruction. -/
def NoFiniteMapFromSFlatOverR {R S : Type u} [CommRing R] [CommRing S]
    (rToS : R →+* S) : Prop :=
  ∀ (T : Type u) [CommRing T] (sToT : S →+* T),
    RingHom.Finite sToT → ¬ RingHom.Flat (sToT.comp rToS)

/-- Finite presentation gives the required stage factorization in a filtered colimit. -/
theorem finitePresentation_factors_through_filtered_stage
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    {f : A →+* B} (D : FilteredFinitelyPresentedFlatColimit f)
    (rToS : A →+* S) (sToB : S →+* B)
    (hfp : RingHom.FinitePresentation rToS)
    (hcompat : sToB.comp rToS = f) :
    FactorsThroughFilteredStage D rToS sToB := by
  sorry

/-- The two obstruction assertions rule out the filtered-colimit presentation. -/
theorem no_filtered_colimit_of_slicing_and_nonflat
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    {f : A →+* B} (D : FilteredFinitelyPresentedFlatColimit f)
    (rToS : A →+* S) (sToB : S →+* B)
    (hfp : RingHom.FinitePresentation rToS)
    (hcompat : sToB.comp rToS = f)
    (hslice : SlicingAssertion rToS)
    (hnonflat : NoFiniteMapFromSFlatOverR rToS) : False := by
  sorry

theorem not_filteredColimit_of_slicing_and_nonflat
    {A S B : Type u} [CommRing A] [CommRing S] [CommRing B]
    {f : A →+* B} (rToS : A →+* S) (sToB : S →+* B)
    (hfp : RingHom.FinitePresentation rToS)
    (hcompat : sToB.comp rToS = f)
    (hslice : SlicingAssertion rToS)
    (hnonflat : NoFiniteMapFromSFlatOverR rToS) :
    ¬ IsFilteredColimitOfFinitelyPresentedFlat f := by
  intro hcolimit
  obtain ⟨D⟩ := hcolimit
  exact no_filtered_colimit_of_slicing_and_nonflat D rToS sToB hfp hcompat hslice hnonflat

/-! ## The henselian local reduction and the cone over an ordinary abelian surface -/

/- The source's strict henselization is represented using the canonical stalk of
   the affine scheme at the chosen origin. -/
structure StrictHenselizationAtPolynomialOrigin (p n : ℕ) [Fact p.Prime] where
  ring : Type
  [ringCommRing : CommRing ring]
  [ringHenselian : HenselianLocalRing ring]
  [ringDomain : IsDomain ring]
  [ringRegular : IsRegularLocalRing ring]
  point : polynomialOriginScheme p n
  point_is_origin : point.asIdeal = polynomialOriginIdeal p n
  map : (polynomialOriginScheme p n).presheaf.stalk point →+* ring
  isStrictHenselization :
    IsStrictHenselization
      ((polynomialOriginScheme p n).presheaf.stalk point) ring map
  residueField_is_algebraicClosure :
    Nonempty (IsLocalRing.ResidueField ring ≃+* AlgebraicClosure (ZMod p))

theorem exists_strictHenselization_at_polynomial_origin (p n : ℕ) [Fact p.Prime] :
    Nonempty (StrictHenselizationAtPolynomialOrigin p n) := by
  sorry

/-- An ordinary abelian surface over an algebraically closed field. -/
structure OrdinaryAbelianSurfaceOver (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (CommRingCat.of k)
  isAbelianSurface : Prop
  isOrdinary : Prop

/- The graded pieces and the coordinate ring are retained so the displayed
   section-ring formula is an actual additive equivalence. -/
structure VeryAmpleLineBundle {k : Type u} [Field k]
    (X : OrdinaryAbelianSurfaceOver k) where
  sectionSpace : ℕ → Type u
  [sectionSpaceAddCommGroup : ∀ n, AddCommGroup (sectionSpace n)]
  [sectionSpaceModule : ∀ n, Module k (sectionSpace n)]
  isLineBundle : Prop
  isVeryAmple : Prop
  sufficientlyPositive : Prop
  sectionRing : CommRingCat.{u}
  sectionRing_structureMap : CommRingCat.of k ⟶ sectionRing
  sectionRing_finiteType :
    RingHom.FiniteType sectionRing_structureMap.hom
  sectionRing_addEquiv :
    Nonempty ((sectionRing : Type u) ≃+ (⨁ n : ℕ, sectionSpace n))
  sectionRing_isAffineCone : Prop

theorem VeryAmpleLineBundle.sectionRing_isNormal
    {k : Type u} [Field k] {X : OrdinaryAbelianSurfaceOver k}
    (L : VeryAmpleLineBundle X) (hL : L.sufficientlyPositive) :
    IsDomain (L.sectionRing : Type u) ∧ IsIntegrallyClosed (L.sectionRing : Type u) := by
  sorry

structure OrdinaryAbelianSurfaceLineBundleData (p : ℕ) [Fact p.Prime] where
  baseField : Type u
  [fieldStructure : Field baseField]
  [fieldAlgebraicallyClosed : IsAlgClosed baseField]
  [fieldCharacteristic : CharP baseField p]
  field_is_algebraicClosureOfPrimeField : Prop
  surface : OrdinaryAbelianSurfaceOver baseField
  lineBundle : VeryAmpleLineBundle surface

theorem exists_ordinary_abelian_surface_line_bundle (p : ℕ) [Fact p.Prime] :
    Nonempty (OrdinaryAbelianSurfaceLineBundleData p) := by
  sorry

/- The existential above is intentionally not used for the main interfaces: the
   chosen surface and its line bundle are passed explicitly below. -/

structure HenselizationAtConeVertex {k : Type u} [Field k]
    {X : OrdinaryAbelianSurfaceOver k} (L : VeryAmpleLineBundle X) where
  vertex : Ideal L.sectionRing
  [vertex_isPrime : vertex.IsPrime]
  [vertex_isMaximal : vertex.IsMaximal]
  ring : CommRingCat.{u}
  [ringHenselian : HenselianLocalRing (ring : Type u)]
  [ringDomain : IsDomain (ring : Type u)]
  [ringIntegrallyClosed : IsIntegrallyClosed (ring : Type u)]
  [ringNoetherian : IsNoetherianRing (ring : Type u)]
  dimension : ringKrullDim (ring : Type u) = 3
  map : Localization.AtPrime vertex →+* (ring : Type u)
  isHenselization :
    IsHenselization (Localization.AtPrime vertex) (ring : Type u) map

/-- The map from the section ring to its henselization at the cone vertex. -/
noncomputable def sectionRingToConeHenselization
    {k : Type u} [Field k] {X : OrdinaryAbelianSurfaceOver k}
    {L : VeryAmpleLineBundle X} (S : HenselizationAtConeVertex L) :
    L.sectionRing →+* (S.ring : Type u) :=
  letI : S.vertex.IsPrime := S.vertex_isPrime
  S.map.comp (algebraMap L.sectionRing (Localization.AtPrime S.vertex))

/- The finite injective map coming from henselized Noether normalization. -/
structure FiniteInjectiveNoetherNormalization (R S : Type u)
    [CommRing R] [CommRing S] where
  map : R →+* S
  finite : RingHom.Finite map
  finitelyPresented : RingHom.FinitePresentation map
  injective : Function.Injective map
  isHenselizedNoetherNormalization : Prop

/- The embedding of the cone ring in the absolute integral closure, together
   with the fact that the same target is absolute over the cone ring. -/
structure AbsoluteIntegralClosureEmbeddingData
    (R S Rplus : Type u) [CommRing R] [CommRing S] [CommRing Rplus]
    (rToS : R →+* S) (rToPlus : R →+* Rplus) where
  sToPlus : S →+* Rplus
  injective : Function.Injective sToPlus
  compatibility : sToPlus.comp rToS = rToPlus
  isAbsoluteIntegralClosure : IsAbsoluteIntegralClosureOf S Rplus sToPlus

theorem exists_absoluteIntegralClosureEmbedding_of_noether_normalization
    (R S : Type u) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S]
    (rToS : R →+* S) (hfinite : RingHom.Finite rToS)
    (hinjective : Function.Injective rToS) :
    Nonempty
      (AbsoluteIntegralClosureEmbeddingData R S (absoluteIntegralClosure R)
        rToS (absoluteIntegralClosureMap R)) := by
  sorry

/-! ## The cohomological obstruction -/

/-- A module with a specified finite free rank. -/
def FiniteFreeOfRank (R : Type v) (M : Type u) [Semiring R] [AddCommMonoid M]
    [Module R M] (n : ℕ) : Prop :=
  Nonempty (Module.Basis (Fin n) R M)

/-- Trace followed by pullback is multiplication by the degree on `H¹`. -/
structure EtaleTraceData (G₁ G₂ : Type u) [AddCommGroup G₁] [AddCommGroup G₂] where
  degree : ℕ
  pullback : G₁ →+ G₂
  trace : G₂ →+ G₁
  degree_positive : 0 < degree
  trace_pullback : trace.comp pullback = nsmulAddMonoidHom (α := G₁) degree

/-- The no-`R¹ lim` comparison and reduction to mod `p` in the source. -/
structure EtaleInverseLimitData (G : Type u) [AddCommGroup G] where
  modP : Type u
  [modPAddCommGroup : AddCommGroup modP]
  inverseLimit : Type u
  [inverseLimitAddCommGroup : AddCommGroup inverseLimit]
  comparison : Nonempty (G ≃+ inverseLimit)
  reduction : G →+ modP
  modP_nontrivial : Nontrivial modP

/-- The finite-surjective cover, trace, inverse-limit, and Artin--Schreier data. -/
structure FinitePuncturedCoverCohomologyData
    (U : Scheme.{u}) (G_U G_V : Type u)
    [AddCommGroup G_U] [AddCommGroup G_V] where
  V : Scheme.{u}
  mapToU : V ⟶ U
  finite_surjective : Prop
  H1EtaleZp_V_nontrivial : Nontrivial G_V
  traceData : EtaleTraceData G_U G_V
  inverseLimitData : EtaleInverseLimitData G_V
  H1O_V : Type u
  [H1O_V_addCommGroup : AddCommGroup H1O_V]
  H1EtaleModP_V : Type u
  [H1EtaleModP_V_addCommGroup : AddCommGroup H1EtaleModP_V]
  H1O_V_nontrivial : Nontrivial H1O_V
  H1O_V_to_H1EtaleModP_V : Nonempty (H1O_V ≃+ H1EtaleModP_V)

/- The geometric package records exactly the displayed comparisons for `U` and
   the ordinary abelian surface `X`. -/
structure OrdinaryAbelianSurfaceCohomologyData
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k]
    (X : OrdinaryAbelianSurfaceOver k)
    (L : VeryAmpleLineBundle X) where
  U : Scheme.{u}
  mapToX : U ⟶ X.scheme
  H1O_U : Type u
  [H1O_U_addCommGroup : AddCommGroup H1O_U]
  H1O_X : Type u
  [H1O_X_addCommGroup : AddCommGroup H1O_X]
  H1O_comparison : Nonempty (H1O_U ≃+ H1O_X)
  H1EtaleZp_U : Type u
  [H1EtaleZp_U_addCommGroup : AddCommGroup H1EtaleZp_U]
  [H1EtaleZp_U_module : Module (ℤ_[p]) H1EtaleZp_U]
  H1EtaleZp_X : Type u
  [H1EtaleZp_X_addCommGroup : AddCommGroup H1EtaleZp_X]
  [H1EtaleZp_X_module : Module (ℤ_[p]) H1EtaleZp_X]
  H1EtaleZp_comparison : Nonempty (H1EtaleZp_U ≃+ H1EtaleZp_X)
  H1EtaleZp_U_finiteFree_rank_two :
    FiniteFreeOfRank (ℤ_[p]) H1EtaleZp_U 2
  H1EtaleZp_U_torsionFree : Module.IsTorsionFree (ℤ_[p]) H1EtaleZp_U
  H1EtaleModP_U : Type u
  [H1EtaleModP_U_addCommGroup : AddCommGroup H1EtaleModP_U]
  artinSchreierOnH1 : H1O_U →+ H1O_U
  H1EtaleModP_U_kernel_comparison :
    Nonempty (H1EtaleModP_U ≃+ AddMonoidHom.ker artinSchreierOnH1)

/-- The ring-level Artin--Schreier map used in the strict local footnote. -/
def artinSchreierMap (R : Type u) (p : ℕ) [CommRing R] [Fact p.Prime]
    [CharP R p] : R →+ R where
  toFun x := x ^ p - x
  map_zero' := by
    have hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
    simp [hp]
  map_add' x y := by
    simp only [add_pow_expChar]
    simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/- The punctured-spectrum statement also includes the equality of global
   sections with the henselian normal domain. -/
structure PuncturedSpectrumData (p : ℕ) (S : Type u) [CommRing S] [Fact p.Prime]
    [CharP S p] [HenselianLocalRing S] where
  U : Scheme.{u}
  inclusion : U ⟶ Spec (CommRingCat.of S)
  isPuncturedSpectrum : Prop
  isNormal : IsDomain S ∧ IsIntegrallyClosed S
  globalSections : Type u
  [globalSectionsCommRing : CommRing globalSections]
  globalSections_identification : Nonempty (globalSections ≃+* S)
  artinSchreier_surjective : Function.Surjective (artinSchreierMap S p)

/-- The local-cohomology groups used at the end of the non-flatness argument. -/
structure LocalCohomologyObstruction (H1OV H2T H2R : Type u)
    [AddCommGroup H1OV] [AddCommGroup H2T] [AddCommGroup H2R] where
  H1OV_nontrivial : Nontrivial H1OV
  H1OV_to_H2T : Nonempty (H1OV ≃+ H2T)
  H2T_nontrivial : Nontrivial H2T
  H2R_subsingleton : Subsingleton H2R

structure LocalCohomologyObstructionData where
  H1OV : Type u
  [H1OV_addCommGroup : AddCommGroup H1OV]
  H2T : Type u
  [H2T_addCommGroup : AddCommGroup H2T]
  H2R : Type u
  [H2R_addCommGroup : AddCommGroup H2R]
  obstruction : LocalCohomologyObstruction H1OV H2T H2R

/-- Finite maps from the cone ring acquire the cohomological obstruction. -/
theorem finite_map_from_cone_not_flat_of_cohomology
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (rToS : R →+* S) (sToT : S →+* T)
    (hfinite : RingHom.Finite sToT)
    (hcoh : LocalCohomologyObstructionData.{u}) :
    ¬ RingHom.Flat (sToT.comp rToS) := by
  sorry

/- The source's complete cohomological proof is used through this named
   interface.  It packages the trace, inverse-limit, Artin--Schreier, and
   local-cohomology steps above. -/
def EveryFiniteMapHasConeCohomologicalObstruction
    (S : Type u) [CommRing S] : Prop :=
  ∀ (T : Type u) [CommRing T] (sToT : S →+* T),
    RingHom.Finite sToT → Nonempty (LocalCohomologyObstructionData.{u})

theorem cone_no_finite_map_flat_over_henselian_base
    {R S : Type u} [CommRing R] [CommRing S]
    (rToS : R →+* S)
    (hcohomology : EveryFiniteMapHasConeCohomologicalObstruction S) :
    NoFiniteMapFromSFlatOverR rToS := by
  intro T instT sToT hfinite hflat
  obtain ⟨hcoh⟩ := hcohomology T sToT hfinite
  exact (finite_map_from_cone_not_flat_of_cohomology rToS sToT hfinite hcoh) hflat

/-! ## The final existence statement -/

/- The source gives two choices of base.  These bundles keep the ring
   structures as actual instances, so the assertions below are directly usable. -/
structure FiniteTypeFpCounterexample where
  p : ℕ
  [pPrime : Fact p.Prime]
  n : ℕ
  n_at_least_three : 3 ≤ n
  A : Type u
  [commRingA : CommRing A]
  B : Type u
  [commRingB : CommRing B]
  f : A →+* B
  base_equivalence : Nonempty (A ≃+* polynomialRing p n)
  flat : RingHom.Flat f
  not_filtered_colimit : ¬ IsFilteredColimitOfFinitelyPresentedFlat f

/-- The chapter's characteristic-`p` counterexample, with a finite-type base. -/
theorem exists_flat_not_filteredColimit_finiteType_Fp :
    Nonempty FiniteTypeFpCounterexample := by
  sorry

structure OneDimensionalCharZeroLocalCounterexample where
  A : Type u
  [commRingA : CommRing A]
  [localA : IsLocalRing A]
  [noetherianA : IsNoetherianRing A]
  dimension : ringKrullDim A = 1
  residueCharacteristicZero : CharZero (IsLocalRing.ResidueField A)
  B : Type u
  [commRingB : CommRing B]
  f : A →+* B
  flat : RingHom.Flat f
  not_filtered_colimit : ¬ IsFilteredColimitOfFinitelyPresentedFlat f

/-- The alternative one-dimensional Noetherian local example in characteristic zero. -/
theorem exists_flat_not_filteredColimit_oneDimensional_charZeroLocal :
    Nonempty OneDimensionalCharZeroLocalCounterexample := by
  sorry

structure FlatNonFilteredColimitCounterexample where
  A : Type u
  [commRingA : CommRing A]
  B : Type u
  [commRingB : CommRing B]
  f : A →+* B
  flat : RingHom.Flat f
  not_filtered_colimit : ¬ IsFilteredColimitOfFinitelyPresentedFlat f

/-- A flat algebra need not be a filtered colimit of finitely presented flat algebras. -/
theorem exists_flat_not_filteredColimit :
    Nonempty FlatNonFilteredColimitCounterexample := by
  sorry

end Formalization.«Books.Examples».Unit78
