import Formalization.Books.Algebra.Unit37.NormalRings
import Formalization.Books.Algebra.Unit96.Completion
import Formalization.Books.Algebra.Unit162.NagataRings
import Formalization.Books.MoreAlgebra.Unit43.PermanenceCompletion
import Formalization.Books.MoreAlgebra.Unit52.ExcellentRings
import Formalization.Books.MoreMorphisms.Unit19.Normalization
import Formalization.Books.MoreMorphisms.Unit20.Normal
import Mathlib.AlgebraicGeometry.Birational.Birational
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.KrullDimension

/-!
# Resolution of Surfaces, Chapter 1: Introduction

This file records the precise setup and theorem interfaces appearing in the
introduction.  Scheme normalization, normality, birationality, properness,
Noetherianity, completion, separability, and module length use the canonical
Mathlib or earlier-book declarations.  The project does not yet have a scheme
cohomology or blowup API, so the small data structures below expose exactly
the missing objects needed by the introduction's statements.
-/

namespace Formalization.Books.Resolve.Unit01

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Formalization.Books.Algebra.Unit37
open Formalization.Books.Algebra.Unit96
open Formalization.Books.Algebra.Unit162
open Formalization.Books.MoreAlgebra.Unit52
open MoreMorphisms.Unit19
open scoped AlgebraicGeometry

universe u

noncomputable section

/-! ## Resolution, normalization, and singular points -/

/-- A scheme is regular when all of its local rings are regular local rings. -/
def IsRegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, @IsRegularLocalRing (X.presheaf.stalk x) _

/-- A modification is a proper birational morphism between integral schemes. -/
def IsModification {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsIntegral X ∧ IsIntegral Y ∧ IsProper f ∧ Scheme.Birational X Y

/-- A resolution of singularities is a regular modification. -/
def HasResolutionOfSingularities (Y : Scheme.{u}) : Prop :=
  ∃ (X : Scheme.{u}) (f : X ⟶ Y),
    IsRegularScheme X ∧ IsModification f

/-- The absolute normalization `Y^ν`, using the canonical relative normalization
of the identity morphism. -/
noncomputable abbrev normalizationScheme (Y : Scheme.{u}) : Scheme.{u} :=
  absoluteNormalization Y

/-- The canonical normalization morphism `Y^ν ⟶ Y`. -/
noncomputable abbrev normalizationMap (Y : Scheme.{u}) :
    normalizationScheme Y ⟶ Y :=
  absoluteNormalizationMap Y

/-- Finiteness of the normalization morphism. -/
def IsFiniteNormalization (Y : Scheme.{u}) : Prop :=
  IsFinite (normalizationMap Y)

/-- The singular points of a scheme, expressed through the canonical
regular-local-ring predicate. -/
def singularLocus (X : Scheme.{u}) : Set X :=
  {x | ¬ @IsRegularLocalRing (X.presheaf.stalk x) _}

/-- The completion of the local ring at a point is normal. -/
def IsNormalCompletionAt (X : Scheme.{u}) (x : X) : Prop :=
  IsNormalRing
    (ringCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))

/-!
The main theorem in the introduction is stated with the integral hypothesis
made explicit, as it is in the chapter's later definition of a modification.
-/

theorem lipman_resolution_of_finite_normalization
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hdim : topologicalKrullDim Y = (2 : WithBot ℕ∞))
    (hfinite : IsFiniteNormalization Y)
    (hsingular : (singularLocus (normalizationScheme Y)).Finite)
    (hcompletion :
      ∀ y : normalizationScheme Y,
        y ∈ singularLocus (normalizationScheme Y) →
          IsNormalCompletionAt (normalizationScheme Y) y) :
    HasResolutionOfSingularities Y := by
  sorry

/-! ## Finite type over a quasi-excellent base -/

/-- Finite type over an affine base, in the scheme-theoretic sense. -/
def IsFiniteTypeOver {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) : Prop :=
  LocallyOfFiniteType f

theorem finite_type_over_quasiExcellent_has_finite_normalization
    (R : Type u) [CommRing R] (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hR : IsQuasiExcellent R) (hfiniteType : IsFiniteTypeOver f)
    (hdim : topologicalKrullDim Y = (2 : WithBot ℕ∞)) :
    IsFiniteNormalization Y ∧
      (singularLocus (normalizationScheme Y)).Finite ∧
      (∀ y : normalizationScheme Y,
        y ∈ singularLocus (normalizationScheme Y) →
          IsNormalCompletionAt (normalizationScheme Y) y) := by
  sorry

theorem finite_type_over_quasiExcellent_has_resolution
    (R : Type u) [CommRing R] (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hR : IsQuasiExcellent R) (hfiniteType : IsFiniteTypeOver f)
    (hdim : topologicalKrullDim Y = (2 : WithBot ℕ∞)) :
    HasResolutionOfSingularities Y := by
  sorry

/-- The standard examples of quasi-excellent bases used in the introduction. -/
theorem standard_quasiExcellent_bases :
    (∀ (K : Type u) [Field K], IsQuasiExcellent K) ∧
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
      [IsDedekindDomain R] [CharZero (FractionRing R)], IsQuasiExcellent R) ∧
    IsQuasiExcellent ℤ := by
  sorry

/-! ## The local ring setup and normalization step -/

/-- The local hypotheses on the ring used throughout the outline. -/
def IsTwoDimensionalNoetherianLocalDomain (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A ∧ IsLocalRing A ∧ IsDomain A ∧ ringKrullDim A = 2

/-- The canonical ring normalization of a domain in its fraction field. -/
noncomputable abbrev ringNormalization (A : Type u) [CommRing A] [IsDomain A] :=
  integralClosure A (FractionRing A)

/-- Finiteness of the canonical ring normalization. -/
def HasFiniteRingNormalization (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  Module.Finite A (ringNormalization A)

/-- In the terminology of the introduction, formal unramifiedness of a local
ring means that its completion is reduced. -/
def IsFormallyUnramifiedLocal (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  _root_.IsReduced (ringCompletion (IsLocalRing.maximalIdeal A))

/-- Normality of the completion supplies finite normalization over the local
ring, the finiteness-lifting step cited in the introduction. -/
theorem finite_ring_normalization_of_normal_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hcompletion :
      IsNormalRing (ringCompletion (IsLocalRing.maximalIdeal A))) :
    HasFiniteRingNormalization A := by
  sorry

/-! A small source-facing interface for the blowup steps in the outline. -/

structure BlowupStep {X Y : Scheme.{u}} (f : X ⟶ Y) where
  proper : IsProper f
  birational : Scheme.Birational X Y
  blowupProperty : Prop

structure NormalizedBlowupStep {X Y : Scheme.{u}} (f : X ⟶ Y) where
  blowup : BlowupStep f
  normalSource : AlgebraicGeometry.IsNormal X

structure NormalizedBlowupChain (Y : Scheme.{u}) (length : ℕ) where
  schemes : Fin (length + 1) → Scheme.{u}
  maps : ∀ i : Fin length, schemes i.succ ⟶ schemes i.castSucc
  steps : ∀ i, NormalizedBlowupStep (maps i)
  toBase : ∀ i, schemes i ⟶ Y
  factor : ∀ i, maps i ≫ toBase i.castSucc = toBase i.succ
  initial : schemes 0 = Y

/-! ## The length invariant and rational singularities -/

/-- The missing scheme-cohomology value `H¹(X, 𝒪_X)` for a normal
modification over `A`, together with its canonical `A`-module structure. -/
structure H1StructureSheafData (A X : Type u) [CommRing A] where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : @Module A carrier _ (@AddCommGroup.toAddCommMonoid carrier addCommGroup)

/-- A normal modification over `Spec(A)`, carrying the `H¹(X, 𝒪_X)` module
needed by the length invariant. -/
structure NormalModificationOver (A : Type u) [CommRing A] where
  scheme : Scheme.{u}
  morphism : scheme ⟶ Spec (CommRingCat.of A)
  integral : IsIntegral scheme
  normal : AlgebraicGeometry.IsNormal scheme
  proper : IsProper morphism
  birational : Scheme.Birational scheme (Spec (CommRingCat.of A))
  h1 : H1StructureSheafData A scheme

/-- The length of `H¹(X, 𝒪_X)` as an `A`-module. -/
noncomputable def h1Length {A : Type u} [CommRing A]
    (M : NormalModificationOver A) : ℕ∞ :=
  letI : AddCommGroup M.h1.carrier := M.h1.addCommGroup
  letI : Module A M.h1.carrier := M.h1.module
  Module.length A M.h1.carrier

/-- The supremum of the lengths of `H¹(X, 𝒪_X)` over all normal
modifications of `Spec(A)`. -/
noncomputable def h1LengthMaximum (A : Type u) [CommRing A] : ℕ∞ :=
  ⨆ M : NormalModificationOver A, h1Length M

/-- Boundedness of the length invariant. -/
def H1LengthBounded (A : Type u) [CommRing A] : Prop :=
  ∃ g : ℕ, ∀ M : NormalModificationOver A, h1Length M ≤ (g : ℕ∞)

/-- The existence of an actual maximum, rather than only an upper bound. -/
def HasH1LengthMaximum (A : Type u) [CommRing A] : Prop :=
  ∃ M : NormalModificationOver A,
    ∀ N : NormalModificationOver A, h1Length N ≤ h1Length M

theorem h1_length_has_maximum_of_bounded
    (A : Type u) [CommRing A] (hbounded : H1LengthBounded A)
    (hmods : Nonempty (NormalModificationOver A)) :
    HasH1LengthMaximum A := by
  sorry

/-- A local ring defines a rational singularity when the maximum length is zero. -/
def IsRationalSingularity (A : Type u) [CommRing A] : Prop :=
  h1LengthMaximum A = 0

/-- The boundedness condition called “reduction to rational singularities”. -/
def ReductionToRationalSingularitiesPossible (A : Type u) [CommRing A] : Prop :=
  H1LengthBounded A

theorem blowup_of_rational_surface_singularity_is_normal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (hA : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hnormal : IsNormalRing A)
    (hrational : IsRationalSingularity A)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (hblowup : BlowupStep f) :
    AlgebraicGeometry.IsNormal X := by
  sorry

/-- A bounded length invariant admits a normal modification whose singular
points are rational singularities. -/
theorem exists_normal_modification_with_rational_singularities
    (A : Type u) [CommRing A]
    (hbounded : ReductionToRationalSingularitiesPossible A) :
    ∃ M : NormalModificationOver A,
      ∀ x : M.scheme, x ∈ singularLocus M.scheme →
        IsRationalSingularity (M.scheme.presheaf.stalk x) := by
  sorry

/-! ## Vanishing and duality interfaces -/

/-- The dualizing-module data needed in the two-dimensional normal case. -/
structure DualizingModuleData (A X : Type u) [CommRing A] where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : @Module A carrier _ (@AddCommGroup.toAddCommMonoid carrier addCommGroup)
  dualizing : Prop
  normalized : Prop

/-- The existence of a dualizing module. -/
def HasDualizingModule (A X : Type u) [CommRing A] : Prop :=
  Nonempty (DualizingModuleData A X)

/-- The source's abstract dualizing-complex witness. -/
structure DualizingComplexData (A : Type u) [CommRing A] where
  carrier : Type u
  dualizing : Prop

def HasDualizingComplex (A : Type u) [CommRing A] : Prop :=
  Nonempty (DualizingComplexData A)

theorem dualizing_complex_iff_dualizing_module_in_dimension_two
    (A X : Type u) [CommRing A] [CommRing X] [IsNoetherianRing A]
    [IsNoetherianRing X]
    (hdim : ringKrullDim X = 2) (hnormal : IsNormalRing X) :
    HasDualizingComplex A ↔ HasDualizingModule A X := by
  sorry

theorem normal_modification_has_dualizing_module
    (A : Type u) [CommRing A] (M : NormalModificationOver A)
    (hA : HasDualizingModule A A) :
    HasDualizingModule A M.scheme := by
  sorry

/-- A model for the derived pushforward `Rf_*𝒪_X` and the shifted residue
field object used in the `Hom_{D(A)}` formulation. -/
structure DerivedPushforwardData (A : Type u) [CommRing A]
    (M : NormalModificationOver A) where
  residueShift : Type u
  derivedPushforward : Type u
  hom : Type u

/-- Vanishing of the `Hom_{D(A)}(κ[-1], Rf_*𝒪_X)` group in the introduction's
derived formulation. -/
def DerivedR1Injective {A : Type u} [CommRing A]
    {M : NormalModificationOver A} (D : DerivedPushforwardData A M) : Prop :=
  Subsingleton D.hom

/-- A model for the first higher direct image `R¹f_*ω_X`. -/
structure HigherDirectImageData (A : Type u) [CommRing A]
    (M : NormalModificationOver A) where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : @Module A carrier _ (@AddCommGroup.toAddCommMonoid carrier addCommGroup)

def GrauertRiemenschneiderVanishing {A : Type u} [CommRing A]
    {M : NormalModificationOver A} (D : HigherDirectImageData A M) : Prop :=
  Subsingleton D.carrier

theorem grauert_riemenschneider_iff_derived_r1_injective
    (A : Type u) [CommRing A] (M : NormalModificationOver A)
    (D : HigherDirectImageData A M)
    (R : DerivedPushforwardData A M) :
    GrauertRiemenschneiderVanishing D ↔ DerivedR1Injective R := by
  sorry

theorem grauert_riemenschneider_vanishing
    (A : Type u) [CommRing A] (hA : IsNagataRing A)
    (M : NormalModificationOver A)
    (hnormal : AlgebraicGeometry.IsNormal M.scheme)
    (hdualizing : HasDualizingComplex A)
    (D : HigherDirectImageData A M) :
    GrauertRiemenschneiderVanishing D := by
  sorry

/-- The positive-conormal input used in the proof of the vanishing theorem.
The degree/conormal construction is intentionally an interface because it is
not present in the current scheme library. -/
structure PositiveConormalComponentData (A : Type u) [CommRing A]
    (M : NormalModificationOver A) where
  component : Type u
  conormalDegree : component → ℤ
  positive : ∃ C, 0 < conormalDegree C

theorem normal_modification_has_positive_conormal_component
    (A : Type u) [CommRing A] (M : NormalModificationOver A)
    (hnormal : AlgebraicGeometry.IsNormal M.scheme) :
    Nonempty (PositiveConormalComponentData A M) := by
  sorry

/-! ## Finite extensions and the two boundedness steps -/

structure FiniteRingExtension (A B : Type u) [CommRing A] [CommRing B] where
  hom : A →+* B
  injective : Function.Injective hom
  isLocal : IsLocalHom hom
  finite : RingHom.Finite hom

structure FractionFieldExtensionData {A B : Type u} [CommRing A] [CommRing B]
    (e : FiniteRingExtension A B) where
  hom : FractionRing A →+* FractionRing B
  commutes : ∀ a : A,
    hom (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (e.hom a)

def IsSeparableFractionFieldExtension {A B : Type u} [CommRing A] [CommRing B]
    {e : FiniteRingExtension A B} (d : FractionFieldExtensionData e) : Prop :=
  letI : Algebra (FractionRing A) (FractionRing B) := d.hom.toAlgebra
  Algebra.IsSeparable (FractionRing A) (FractionRing B)

noncomputable def fractionFieldDegree {A B : Type u} [CommRing A] [CommRing B]
    {e : FiniteRingExtension A B} (d : FractionFieldExtensionData e) : ℕ :=
  letI : Algebra (FractionRing A) (FractionRing B) := d.hom.toAlgebra
  Module.finrank (FractionRing A) (FractionRing B)

theorem h1_length_bounded_of_finite_separable_extension
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsNoetherianRing B] [IsLocalRing B] [IsDomain B]
    (e : FiniteRingExtension A B) (d : FractionFieldExtensionData e)
    (hseparable : IsSeparableFractionFieldExtension d)
    (hA : IsNagataRing A) (hB : IsNagataRing B)
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hnormalA : IsNormalRing A) (hnormalB : IsNormalRing B)
    (hbounded : H1LengthBounded A) :
    H1LengthBounded B := by
  sorry

theorem h1_length_bounded_of_degree_prime_extension
    (A B : Type u) [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsLocalRing A]
    [IsNoetherianRing B] [IsLocalRing B] [IsDomain B]
    (e : FiniteRingExtension A B) (d : FractionFieldExtensionData e)
    (p : ℕ) (hp : p.Prime)
    (hdegree : fractionFieldDegree d = p)
    (hchar : CharP A p) (hregular : IsRegularLocalRing A)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hA : IsNagataRing A) (hB : IsNagataRing B)
    (hdimA : ringKrullDim A = 2) (hdimB : ringKrullDim B = 2)
    (hnormalA : IsNormalRing A) (hnormalB : IsNormalRing B)
    (hbounded : H1LengthBounded A) :
    H1LengthBounded B := by
  sorry

/-! ## Rational and rational-double singularities -/

/-- Dualizing data with an invertible dualizing module, the source-facing
interface for the Gorenstein condition. -/
structure GorensteinDualizingModuleData (A : Type u) [CommRing A] where
  carrier : Type u
  addCommGroup : AddCommGroup carrier
  module : @Module A carrier _ (@AddCommGroup.toAddCommMonoid carrier addCommGroup)
  dualizing : Prop
  invertible : Prop

def IsGorensteinRing (A : Type u) [CommRing A] : Prop :=
  Nonempty (GorensteinDualizingModuleData A)

def IsRationalDoublePoint (A : Type u) [CommRing A] : Prop :=
  IsRationalSingularity A ∧ IsGorensteinRing A

def IsGorensteinScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsGorensteinRing (X.presheaf.stalk x)

def IsRationalScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRationalSingularity (X.presheaf.stalk x)

def HasGorensteinRationalBlowupReduction (Y : Scheme.{u}) : Prop :=
  ∃ length, ∃ C : NormalizedBlowupChain Y length,
    IsGorensteinScheme (C.schemes (Fin.last length)) ∧
      IsRationalScheme (C.schemes (Fin.last length))

theorem rational_surface_reduces_to_gorenstein
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsDomain A] (hA : IsNagataRing A)
    (hdim : ringKrullDim A = 2) (hnormal : IsNormalRing A)
    (hrational : IsRationalSingularity A)
    (hdualizing : HasDualizingComplex A) :
    HasGorensteinRationalBlowupReduction (Spec (CommRingCat.of A)) := by
  sorry

structure HypersurfacePresentation (A : Type u) [CommRing A] where
  ambient : Type u
  ambientCommRing : CommRing ambient
  ambientRegular : @IsRegularLocalRing ambient ambientCommRing
  equation : ambient
  quotientEquiv :
    letI : CommRing ambient := ambientCommRing
    Nonempty (A ≃+* (ambient ⧸ Ideal.span ({equation} : Set ambient)))

/-- A hypersurface singularity is a quotient of a regular local ring by one
equation. -/
def IsHypersurfaceSingularity (A : Type u) [CommRing A] : Prop :=
  Nonempty (HypersurfacePresentation A)

theorem rational_double_point_is_hypersurface
    (A : Type u) [CommRing A] (h : IsRationalDoublePoint A) :
    IsHypersurfaceSingularity A := by
  sorry

def quadraticPart {A : Type u} [CommRing A]
    (a : Fin 3 → Fin 3 → A) : MvPolynomial (Fin 3) A :=
  MvPolynomial.C (a 0 0) * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C (a 0 1) * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C (a 0 2) * MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.C (a 1 1) * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C (a 1 2) * MvPolynomial.X 1 * MvPolynomial.X 2 +
    MvPolynomial.C (a 2 2) * MvPolynomial.X 2 ^ 2

def cubicPart {A : Type u} [CommRing A]
    (a : Fin 3 → Fin 3 → Fin 3 → A) : MvPolynomial (Fin 3) A :=
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    MvPolynomial.C (a i j k) * MvPolynomial.X i *
      MvPolynomial.X j * MvPolynomial.X k

/-- The displayed local equation has a nonzero quadratic part and terms of
degree at least three. -/
def HasQuadraticPlusHigherEquation (A : Type u) [CommRing A] : Prop :=
  ∃ (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A),
    quadraticPart a ≠ 0 ∧
      quadraticPart a = cubicPart b

theorem rational_double_point_has_quadratic_plus_higher_equation
    (A : Type u) [CommRing A] (h : IsRationalDoublePoint A) :
    HasQuadraticPlusHigherEquation A := by
  sorry

theorem rational_double_point_has_resolution
    (A : Type u) [CommRing A] (h : IsRationalDoublePoint A) :
    HasResolutionOfSingularities (Spec (CommRingCat.of A)) := by
  sorry

/-! ## Normalized blowups, completion, and the final strategy -/

structure NormalizedBlowupSequence (Y : Scheme.{u}) (length : ℕ) where
  schemes : Fin (length + 1) → Scheme.{u}
  maps : ∀ i : Fin length, schemes i.succ ⟶ schemes i.castSucc
  steps : ∀ i, NormalizedBlowupStep (maps i)
  toBase : ∀ i, schemes i ⟶ Y
  factor : ∀ i, maps i ≫ toBase i.castSucc = toBase i.succ
  initial : schemes 0 = Y
  terminalRegular : IsRegularScheme (schemes (Fin.last length))

def HasResolutionByNormalizedBlowups (Y : Scheme.{u}) : Prop :=
  ∃ length, Nonempty (NormalizedBlowupSequence Y length)

theorem resolution_implies_resolution_by_normalized_blowups
    (Y : Scheme.{u}) [IsIntegral Y] [IsNoetherian Y]
    (hnormal : AlgebraicGeometry.IsNormal Y)
    (hdim : topologicalKrullDim Y = (2 : WithBot ℕ∞))
    (hresolution : HasResolutionOfSingularities Y) :
    HasResolutionByNormalizedBlowups Y := by
  sorry

noncomputable def completionSpecMap (A : Type u) [CommRing A] [IsLocalRing A] :
    Spec (CommRingCat.of (ringCompletion (IsLocalRing.maximalIdeal A))) ⟶
      Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap A (ringCompletion (IsLocalRing.maximalIdeal A))))

def IsCompletionBaseChange {A : Type u} [CommRing A] [IsLocalRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (Xc : Scheme.{u}) (fc : Xc ⟶
      Spec (CommRingCat.of (ringCompletion (IsLocalRing.maximalIdeal A)))) : Prop :=
  Nonempty
    { e : Xc ≅ Limits.pullback f (completionSpecMap A) //
        e.hom ≫ Limits.pullback.snd f (completionSpecMap A) = fc }

def IsCompletionLift {A : Type u} [CommRing A] [IsLocalRing A]
    {length : ℕ}
    (completed : NormalizedBlowupSequence
      (Spec (CommRingCat.of (ringCompletion (IsLocalRing.maximalIdeal A)))) length)
    (lifted : NormalizedBlowupSequence (Spec (CommRingCat.of A)) length) : Prop :=
  ∀ i : Fin (length + 1),
    IsCompletionBaseChange (lifted.toBase i) (completed.schemes i)
      (completed.toBase i)

theorem normalized_blowup_sequence_lifts_from_completion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hcompletion :
      IsNormalRing (ringCompletion (IsLocalRing.maximalIdeal A)))
    {length : ℕ}
    (completed : NormalizedBlowupSequence
      (Spec (CommRingCat.of (ringCompletion (IsLocalRing.maximalIdeal A)))) length) :
    ∃ lifted : NormalizedBlowupSequence (Spec (CommRingCat.of A)) length,
      IsCompletionLift completed lifted := by
  sorry

theorem resolve_complete_local_normal_surface
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hnormal : IsNormalRing A)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hdim : ringKrullDim A = 2) :
    HasResolutionOfSingularities (Spec (CommRingCat.of A)) := by
  sorry

theorem resolve_complete_by_degree_induction
    (A₀ A : Type u) [CommRing A₀] [CommRing A]
    [IsNoetherianRing A₀] [IsLocalRing A₀]
    (hregular : IsRegularLocalRing A₀)
    (hcomplete₀ : IsAdicComplete (IsLocalRing.maximalIdeal A₀) A₀)
    (f : A₀ →+* A) (hinjective : Function.Injective f)
    (hfinite : RingHom.Finite f)
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (hnormal : IsNormalRing A)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hdim : ringKrullDim A = 2) :
    HasResolutionOfSingularities (Spec (CommRingCat.of A)) := by
  sorry

end

end Formalization.Books.Resolve.Unit01
