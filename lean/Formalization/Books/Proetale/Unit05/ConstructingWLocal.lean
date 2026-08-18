import Formalization.Books.Proetale.Unit02.SomeTopology
import Formalization.Books.Proetale.Unit04.IndZariski
import Formalization.Books.Algebra.Unit03.BasicNotions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.RingHom.Unramified
import Mathlib.RingTheory.Unramified.Basic

/-!
# Pro-étale Cohomology, Chapter 5: Constructing w-local affine schemes

This file records the construction of the w-localization of an affine scheme.
The topological pieces are represented by subsets of `PrimeSpectrum`; the
affine rings and their filtered colimit use Mathlib's `CommRingCat` limits and
colimits.
-/

namespace Formalization.Books.Proetale.Unit05

open Set Function CategoryTheory CategoryTheory.Limits
open Formalization.Books.Proetale.Unit02
open Formalization.Books.Proetale.Unit04
open Formalization.Books.Topology.Unit22
open Formalization.Books.Topology.Unit24
open _root_.Topology
open scoped BigOperators

universe u v

noncomputable section
section
attribute [local instance] Classical.propDecidable
local instance instDecidableEq (A : Type u) : DecidableEq A := Classical.decEq A

/-! ## Affine w-locality and locally closed pieces -/

/-- An affine scheme is w-local when its spectrum is a w-local space. -/
def IsWLocalAffine {A : Type u} [CommRing A] : Prop :=
  IsWLocalSpace (PrimeSpectrum A)

def IsWLocalRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  IsWLocalMap (PrimeSpectrum.comap f)

/-- The ordinary unramified ring-map condition, with the canonical algebra
structure induced by a bare ring homomorphism. -/
def IsUnramifiedRingMap {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : Prop :=
  letI := f.toAlgebra
  Algebra.Unramified A B

/-- A locally closed piece of an affine spectrum in the form `D(f) ∩ V(I)`. -/
structure LocallyClosedPiece (A : Type u) [CommRing A] where
  f : A
  I : Ideal A

/-- The underlying set of a locally closed piece. -/
def LocallyClosedPiece.carrier {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.basicOpen Z.f : Set (PrimeSpectrum A)) ∩
    PrimeSpectrum.zeroLocus (Z.I : Set A)

/-- The multiplicative set of elements which are units on `(A/I)_f`. -/
def LocallyClosedPiece.units {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Submonoid A where
  carrier := {a |
    IsUnit (algebraMap (A ⧸ Z.I)
      (Localization.Away (Ideal.Quotient.mk Z.I Z.f))
      (Ideal.Quotient.mk Z.I a))}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simpa [map_mul] using ha.mul hb

/-- The source's ring `A_Z^~`. -/
abbrev localizedPieceRing {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Type u :=
  Localization Z.units

instance localizedPieceRing.commRing {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : CommRing (localizedPieceRing Z) := by
  dsimp [localizedPieceRing]
  infer_instance

def localizedPieceRingHom {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : A →+* localizedPieceRing Z :=
  algebraMap A (localizedPieceRing Z)

instance localizedPieceRing.algebra {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Algebra A (localizedPieceRing Z) :=
  (localizedPieceRingHom Z).toAlgebra

/-- The points of `Spec(A)` specializing to a subset. -/
def pointsSpecializingToPiece {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  pointsSpecializingTo Z.carrier

abbrev LocallyClosedPointSpace {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) :=
  {x : PrimeSpectrum A // x ∈ pointsSpecializingToPiece Z}

instance locallyClosedPointSpace.topologicalSpace
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    TopologicalSpace (LocallyClosedPointSpace Z) :=
  TopologicalSpace.induced Subtype.val inferInstance

def localizedPieceSpectrumMap {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) :
    PrimeSpectrum (localizedPieceRing Z) → PrimeSpectrum A :=
  PrimeSpectrum.comap (localizedPieceRingHom Z)

/-- The closed-locus predicate used for affine closed subschemes. -/
def IsClosedAffineLocus {R : Type u} [CommRing R]
    (T : Set (PrimeSpectrum R)) : Prop := IsClosed T

theorem localizedPieceRing_quotient_equiv_localizedQuotient
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Nonempty
      ((localizedPieceRing Z ⧸
          Ideal.map (localizedPieceRingHom Z) Z.I) ≃+*
        Localization (Z.units.map (Ideal.Quotient.mk Z.I))) := by
  exact Formalization.Books.Algebra.Unit03.localized_ideal_quotient_equiv
    Z.units Z.I

theorem localizedPieceRing_closedQuotient_equiv_away
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    Nonempty
      ((localizedPieceRing Z ⧸
          Ideal.map (localizedPieceRingHom Z) Z.I) ≃+*
        Localization.Away (Ideal.Quotient.mk Z.I Z.f)) := by
  sorry

/-! ## The localization lemma -/

/-- The localization identifies its spectrum with the points specializing to
the chosen locally closed piece, and the piece becomes closed. -/
theorem localization_piece_properties
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    ∃ e : PrimeSpectrum (Localization Z.units) ≃ₜ
        LocallyClosedPointSpace Z,
      (∀ x, (e x : PrimeSpectrum A) = localizedPieceSpectrumMap Z x) ∧
        IsClosedAffineLocus
          (localizedPieceSpectrumMap Z ⁻¹' Z.carrier) := by
  sorry

theorem localization_piece_has_closed_subscheme
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of (localizedPieceRing Z)),
        AlgebraicGeometry.IsClosedImmersion i ∧
          Set.range i.base =
            (localizedPieceSpectrumMap Z ⁻¹' Z.carrier) := by
  sorry

/-- The ring `A_Z^~` depends only on the underlying locally closed subset. -/
theorem localizedPieceRing_depends_only_on_carrier
    {A : Type u} [CommRing A] (Z Z' : LocallyClosedPiece A)
    (h : Z.carrier = Z'.carrier) :
    Nonempty (localizedPieceRing Z ≃ₐ[A] localizedPieceRing Z') := by
  sorry

/-- Functoriality of the localization along locally closed pieces. -/
def MapsIntoLocallyClosedPiece
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : LocallyClosedPiece A) (Z' : LocallyClosedPiece B) : Prop :=
  ∀ y : PrimeSpectrum B, y ∈ Z'.carrier →
    PrimeSpectrum.comap f y ∈ Z.carrier

theorem exists_localizedPieceRingHom
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (Z : LocallyClosedPiece A) (Z' : LocallyClosedPiece B)
    (h : MapsIntoLocallyClosedPiece f Z Z') :
    ∃! g : localizedPieceRing Z →ₐ[A] localizedPieceRing Z',
      g.toRingHom.comp (localizedPieceRingHom Z) =
        (localizedPieceRingHom Z').comp f := by
  sorry

/-! ## Finite vanishing-pattern stratifications -/

/-- A decomposition `E = E' ⊔ E''` of a finite set. -/
structure StratumPartition {A : Type u} (E : Finset A) where
  nonvanishing : Finset A
  vanishing : Finset A
  disjoint : Disjoint nonvanishing vanishing
  union_eq : nonvanishing ∪ vanishing = E

def stratumPiece {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : LocallyClosedPiece A where
  f := p.nonvanishing.prod id
  I := Ideal.span (↑p.vanishing : Set A)

/-- The stratum with the prescribed vanishing pattern. -/
def stratum {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Set (PrimeSpectrum A) :=
  (stratumPiece p).carrier

theorem mem_stratum_iff_vanishing_pattern
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) (x : PrimeSpectrum A) :
    x ∈ stratum p ↔
      (∀ f ∈ p.nonvanishing, f ∉ x.asIdeal) ∧
        (∀ f ∈ p.vanishing, f ∈ x.asIdeal) := by
  sorry

/-- The displayed description of a stratum as `D(∏ E') ∩ V((E''))`. -/
theorem stratum_eq_basicOpen_inter_zeroLocus
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) :
    stratum p =
      (PrimeSpectrum.basicOpen (p.nonvanishing.prod id) :
        Set (PrimeSpectrum A)) ∩
        PrimeSpectrum.zeroLocus (Ideal.span (↑p.vanishing : Set A) : Set A) := by
  rfl

theorem stratum_isConstructible
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : IsConstructible (stratum p) := by
  sorry

theorem stratum_isLocallyClosed
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : IsLocallyClosed (stratum p) := by
  sorry

/-- The vanishing-pattern strata are pairwise disjoint and cover the spectrum. -/
theorem strata_pairwise_disjoint_and_cover
    {A : Type u} [CommRing A] (E : Finset A) :
    (Pairwise (fun p q : StratumPartition E =>
        Disjoint (stratum p) (stratum q))) ∧
      (⋃ p : StratumPartition E, stratum p) = Set.univ := by
  sorry

/-- A finite constructible stratification. -/
structure FiniteConstructibleStratification (X : Type u)
    [TopologicalSpace X] where
  index : Type u
  finite_index : Finite index
  piece : index → Set X
  pairwise_disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  cover : ⋃ i, piece i = Set.univ
  constructible : ∀ i, IsConstructible (piece i)

/-- Every finite constructible stratification of an affine spectrum is
refined by a finite vanishing-pattern stratification. -/
theorem exists_stratum_refinement
    {A : Type u} [CommRing A]
    (S : FiniteConstructibleStratification (PrimeSpectrum A)) :
    ∃ E : Finset A, ∀ p : StratumPartition E, ∃ i : S.index,
      stratum p ⊆ S.piece i := by
  sorry

/-! ## The finite stages -/

/-- The localized factor belonging to a stratum. -/
def stratumFactor {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Type u :=
  localizedPieceRing (stratumPiece p)

instance stratumFactor.commRing {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : CommRing (stratumFactor p) := by
  dsimp [stratumFactor]
  infer_instance

instance stratumFactor.algebra {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Algebra A (stratumFactor p) := by
  dsimp [stratumFactor]
  infer_instance

def stratumFactorDiagram {A : Type u} [CommRing A] (E : Finset A) :
    Discrete (StratumPartition E) ⥤ CommRingCat :=
  Discrete.functor (fun p : StratumPartition E =>
    CommRingCat.of (stratumFactor p))

/-- The product ring `A_E` of the localized strata. -/
noncomputable def stageRing {A : Type u} [CommRing A] (E : Finset A) : CommRingCat :=
  limit (stratumFactorDiagram E)

/-- The disjoint-union presentation of the spectrum of `A_E`. -/
def stageSpectrum {A : Type u} [CommRing A] (E : Finset A) : Type u :=
  Σ p : StratumPartition E, PrimeSpectrum (stratumFactor p)

def stageClosedLocus {A : Type u} [CommRing A] (E : Finset A) :
    Set (stageSpectrum E) :=
  {x | x.2 ∈
    (localizedPieceSpectrumMap (stratumPiece x.1) ⁻¹'
      (stratumPiece x.1).carrier)}

/-- The spectrum of the product is canonically the disjoint union of the
localized spectra. -/
theorem exists_stageSpectrumEquiv
    {A : Type u} [CommRing A] (E : Finset A) :
    Nonempty (stageSpectrum E ≃ₜ PrimeSpectrum (stageRing E)) := by
  sorry

noncomputable def stageSpectrumEquiv
    {A : Type u} [CommRing A] (E : Finset A) :
    stageSpectrum E ≃ₜ PrimeSpectrum (stageRing E) :=
  Classical.choice (exists_stageSpectrumEquiv E)

/-- The structure map from the base ring to a finite stage. -/
noncomputable def stageRingMap {A : Type u} [CommRing A] (E : Finset A) :
    A →+* stageRing E :=
  (limit.lift (stratumFactorDiagram E)
    { pt := CommRingCat.of A
      π := Discrete.natTrans
        (fun p => CommRingCat.ofHom (algebraMap A (stratumFactor p.as))) }).hom

instance stageRing.algebra {A : Type u} [CommRing A] (E : Finset A) :
    Algebra A (stageRing E) :=
  (stageRingMap E).toAlgebra

def stageSpectrumMap {A : Type u} [CommRing A] (E : Finset A) :
    PrimeSpectrum (stageRing E) → PrimeSpectrum A :=
  PrimeSpectrum.comap (stageRingMap E)

/-- The closed subscheme `Z_E`, transported to `Spec(A_E)`. -/
def stageClosedLocusOnSpectrum {A : Type u} [CommRing A] (E : Finset A) :
    Set (PrimeSpectrum (stageRing E)) :=
  stageSpectrumEquiv E '' stageClosedLocus E

theorem stageClosedLocus_isClosed
    {A : Type u} [CommRing A] (E : Finset A) :
    IsClosedAffineLocus (stageClosedLocusOnSpectrum E) := by
  sorry

theorem stageClosedLocus_has_closed_subscheme
    {A : Type u} [CommRing A] (E : Finset A) :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ AlgebraicGeometry.Spec (stageRing E),
        AlgebraicGeometry.IsClosedImmersion i ∧
          Set.range i.base = stageClosedLocusOnSpectrum E := by
  sorry

theorem stageClosedLocus_contains_closedPoints
    {A : Type u} [CommRing A] (E : Finset A) :
    closedPoints (PrimeSpectrum (stageRing E)) ⊆
      stageClosedLocusOnSpectrum E := by
  sorry

theorem stageClosedLocus_every_point_specializes
    {A : Type u} [CommRing A] (E : Finset A) :
    ∀ x : PrimeSpectrum (stageRing E),
      ∃ z ∈ stageClosedLocusOnSpectrum E, x ⤳ z := by
  sorry

/-- The closed locus at a finite stage maps bijectively to the original
spectrum, as in the source's construction. -/
theorem stageClosedLocus_maps_bijectively_to_base
    {A : Type u} [CommRing A] (E : Finset A) :
    Function.Bijective (fun z : stageClosedLocusOnSpectrum E =>
      stageSpectrumMap E z.1) := by
  sorry

/-! ## Transition maps and the w-localization -/

def restrictPartition {A : Type u} {E₁ E₂ : Finset A}
    (h : E₁ ⊆ E₂) (p : StratumPartition E₂) : StratumPartition E₁ where
  nonvanishing := p.nonvanishing.filter (fun a => a ∈ E₁)
  vanishing := p.vanishing.filter (fun a => a ∈ E₁)
  disjoint := by
    exact p.disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  union_eq := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_filter.mp ha).2
      · exact (Finset.mem_filter.mp ha).2
    · intro ha
      have ha' : a ∈ p.nonvanishing ∪ p.vanishing := by
        rw [p.union_eq]
        exact h ha
      rcases Finset.mem_union.mp ha' with ha' | ha'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha', ha⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha', ha⟩))

/-- The transition map between the localized factors. -/
theorem exists_stratumTransition
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂)
    (p : StratumPartition E₂) :
    ∃! g : stratumFactor (restrictPartition h p) →+* stratumFactor p,
      g.comp (localizedPieceRingHom (stratumPiece (restrictPartition h p))) =
        (localizedPieceRingHom (stratumPiece p)).comp (RingHom.id A) := by
  sorry

noncomputable def stratumTransition
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂)
    (p : StratumPartition E₂) :
    stratumFactor (restrictPartition h p) →+* stratumFactor p :=
  Classical.choose (exists_stratumTransition h p)

/-- The induced transition map `A_E₁ → A_E₂`. -/
theorem exists_stageRingHom
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    Nonempty (stageRing E₁ ⟶ stageRing E₂) := by
  sorry

noncomputable def stageRingHom
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stageRing E₁ ⟶ stageRing E₂ :=
  limit.lift (stratumFactorDiagram E₂)
    { pt := stageRing E₁
      π := Discrete.natTrans (fun p =>
        limit.π (stratumFactorDiagram E₁)
            (Discrete.mk (restrictPartition h p.as)) ≫
          CommRingCat.ofHom (stratumTransition h p.as)) }

theorem stageRingHom_commutes_with_base
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    (stageRingHom h).hom.comp (stageRingMap E₁) = stageRingMap E₂ := by
  sorry

def stageScheme {A : Type u} [CommRing A] (E : Finset A) :
    AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (stageRing E)

noncomputable def stageTransitionScheme
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stageScheme E₂ ⟶ stageScheme E₁ := by
  change AlgebraicGeometry.Spec (stageRing E₂) ⟶
    AlgebraicGeometry.Spec (stageRing E₁)
  exact AlgebraicGeometry.Spec.map (stageRingHom h)

def stageTransitionPoints
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    PrimeSpectrum (stageRing E₂) → PrimeSpectrum (stageRing E₁) :=
  PrimeSpectrum.comap (stageRingHom h).hom

theorem stageTransition_maps_closedLocus
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    MapsTo (stageTransitionPoints h) (stageClosedLocusOnSpectrum E₂)
      (stageClosedLocusOnSpectrum E₁) := by
  sorry

/-- The finite stages form the directed system used in the construction. -/
noncomputable def stageFunctor {A : Type u} [CommRing A] :
    Finset A ⥤ CommRingCat :=
  { obj := stageRing
    map := fun {E₁ E₂} h => stageRingHom (leOfHom h)
    map_id := by sorry
    map_comp := by sorry }

def stageFunctorBaseMap {A : Type u} [CommRing A] (E : Finset A) :
    A →+* stageFunctor (A := A).obj E :=
  stageRingMap E

/-- The colimit ring `A_w`. -/
noncomputable def wLocalRing {A : Type u} [CommRing A] : CommRingCat :=
  colimit (stageFunctor (A := A))

/-- The affine scheme `X_w = Spec(A_w)`. -/
def wLocalSpectrum {A : Type u} [CommRing A] : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (wLocalRing (A := A))

/-- The inverse system of affine schemes associated to the finite-stage
colimit diagram. -/
noncomputable def stageSchemeDiagram {A : Type u} [CommRing A] :
    (Finset A)ᵒᵖ ⥤ AlgebraicGeometry.Scheme :=
  (stageFunctor (A := A)).op ⋙ AlgebraicGeometry.Scheme.Spec

theorem stageSchemeDiagram_obj_iso
    {A : Type u} [CommRing A] (E : Finset A) :
    Nonempty (stageSchemeDiagram (A := A).obj (Opposite.op E) ≅
      stageScheme E) := by
  change Nonempty (AlgebraicGeometry.Spec (stageRing E) ≅
    AlgebraicGeometry.Spec (stageRing E))
  exact ⟨Iso.refl _⟩

/-- The canonical cone from `Spec(A_w)` to the finite-stage spectra. -/
noncomputable def wLocalSpectrumStageCone {A : Type u} [CommRing A] :
    Cone (stageSchemeDiagram (A := A)) where
  pt := AlgebraicGeometry.Spec (colimit (stageFunctor (A := A)))
  π := { app := fun E =>
      AlgebraicGeometry.Spec.map (colimit.ι (stageFunctor (A := A)) E.unop)
         naturality := by
           intro E F f
           dsimp [stageSchemeDiagram]
           simp only [Category.id_comp]
           rw [← AlgebraicGeometry.Spec.map_comp, colimit.w] }

theorem wLocalSpectrum_is_limit_of_stage_schemes
    {A : Type u} [CommRing A] :
    Nonempty (IsLimit (wLocalSpectrumStageCone (A := A))) := by
  sorry

noncomputable def wLocalRingMap {A : Type u} [CommRing A] :
    A →+* wLocalRing (A := A) :=
  (colimit.ι (stageFunctor (A := A)) ∅).hom.comp
    (stageFunctorBaseMap (A := A) ∅)

/- The ring map corresponding to the projection from the inverse-limit
   spectrum to the spectrum of a finite stage. -/
noncomputable def wLocalStageRingMap {A : Type u} [CommRing A]
    (E : Finset A) : stageRing E →+* wLocalRing (A := A) :=
  (colimit.ι (stageFunctor (A := A)) E).hom.comp
    (RingHom.id (stageRing E))

/-- The closed subscheme locus `Z` in the source's inverse-limit formula. -/
noncomputable def wLocalClosedLocus {A : Type u} [CommRing A] :
    Set (PrimeSpectrum (wLocalRing (A := A))) :=
  {x | ∀ E : Finset A,
    PrimeSpectrum.comap (wLocalStageRingMap (A := A) E) x ∈
      stageClosedLocusOnSpectrum E}

theorem wLocalClosedLocus_eq_closedPoints
    {A : Type u} [CommRing A] :
    wLocalClosedLocus (A := A) =
      closedPoints (PrimeSpectrum (wLocalRing (A := A))) := by
  sorry

theorem exists_wLocalRingMap {A : Type u} [CommRing A] :
    Nonempty (A →+* wLocalRing (A := A)) := by
  exact ⟨wLocalRingMap (A := A)⟩

def wLocalSpectrumMap {A : Type u} [CommRing A] :
    PrimeSpectrum (wLocalRing (A := A)) → PrimeSpectrum A :=
  PrimeSpectrum.comap (wLocalRingMap (A := A))

theorem exists_wLocal_closedLocus_homeomorph
    {A : Type u} [CommRing A] :
    Nonempty
      {e : wLocalClosedLocus (A := A) ≃ₜ PrimeSpectrum A //
        ∀ z, e z = wLocalSpectrumMap (A := A) z} := by
  sorry

theorem wLocalSpectrumMap_bijective_on_closedLocus
    {A : Type u} [CommRing A] :
    Function.Bijective (fun z : wLocalClosedLocus (A := A) =>
      wLocalSpectrumMap (A := A) z) := by
  sorry

theorem wLocalRing_isIndZariski_and_faithfullyFlat
    {A : Type u} [CommRing A] :
    IsIndZariski (wLocalRingMap (A := A)) ∧
      RingHom.FaithfullyFlat (wLocalRingMap (A := A)) := by
  sorry

theorem wLocalConstruction_properties
    {A : Type u} [CommRing A] :
    IsIndZariski (wLocalRingMap (A := A)) ∧
      RingHom.FaithfullyFlat (wLocalRingMap (A := A)) ∧
        IsWLocalAffine (A := wLocalRing (A := A)) ∧
          Nonempty (wLocalClosedLocus (A := A) ≃ₜ PrimeSpectrum A) ∧
            Function.Bijective (fun z : wLocalClosedLocus (A := A) =>
              wLocalSpectrumMap (A := A) z) ∧
              IsClosed (wLocalClosedLocus (A := A)) ∧
                ∀ x : PrimeSpectrum (wLocalRing (A := A)),
                  ∃! z : wLocalClosedLocus (A := A),
                    x ⤳ (z : PrimeSpectrum (wLocalRing (A := A))) := by
  sorry

theorem wLocalClosedLocus_isClosed
    {A : Type u} [CommRing A] :
    IsClosed (wLocalClosedLocus (A := A)) := by
  sorry

theorem wLocal_closedLocus_is_reduced
    {A : Type u} [CommRing A] :
    ∃ Y : AlgebraicGeometry.Scheme,
      ∃ i : Y ⟶ wLocalSpectrum (A := A),
        AlgebraicGeometry.IsClosedImmersion i ∧ AlgebraicGeometry.IsReduced Y ∧
          Set.range i.base = wLocalClosedLocus (A := A) := by
  sorry

/-! ## The size remark and the universal property -/

theorem wLocalRing_cardinal_le
    {A : Type u} [CommRing A] (κ : Cardinal) (hκ : Cardinal.mk A ≤ κ)
    (hinfinite : ℵ₀ ≤ κ) :
    Cardinal.mk (wLocalRing (A := A)) ≤ κ := by
  sorry

theorem wLocalRing_universal
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hB : IsWLocalAffine (A := B)) :
    ∃! g : wLocalRing (A := A) ⟶ CommRingCat.of B,
      CommRingCat.ofHom (wLocalRingMap (A := A)) ≫ g =
        CommRingCat.ofHom f ∧ IsWLocalRingMap g.hom := by
  sorry

/- The source recalls this characterization before applying it to the
   permanence lemma below. -/
theorem profinite_spectrum_iff_all_points_closed
    {A : Type u} [CommRing A] :
    IsProfiniteSpace (PrimeSpectrum A) ↔
      closedPoints (PrimeSpectrum A) = Set.univ := by
  sorry

/-! ## Profinite spectra and permanence -/

def NoSpecializationInFibres
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ q q' : PrimeSpectrum B,
    PrimeSpectrum.comap f q = PrimeSpectrum.comap f q' →
      q ≤ q' → q = q'

theorem profinite_spectrum_of_fibre_condition
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (h : NoSpecializationInFibres f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

def HasAlgebraicResidueExtensions
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) : Prop :=
  ∀ q : PrimeSpectrum B,
    let I := q.asIdeal.comap f
    letI : I.IsPrime := q.isPrime.comap f
    letI : q.asIdeal.IsPrime := q.isPrime
    let g := Ideal.ResidueField.map I q.asIdeal f rfl
    letI := g.toAlgebra
    Algebra.IsAlgebraic I.ResidueField q.asIdeal.ResidueField

theorem profinite_spectrum_of_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hres : HasAlgebraicResidueExtensions f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_local_isomorphism
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IsLocalIsomorphism f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_identifies_local_rings
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IdentifiesLocalRings f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_weakly_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : letI := f.toAlgebra; Algebra.WeaklyEtale A B) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_quasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : f.QuasiFinite) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_unramified
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : IsUnramifiedRingMap f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : f.Etale) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

noncomputable def filteredColimitRing
    {F : Type v} [Category.{v} F] (G : F ⥤ CommRingCat) : CommRingCat :=
  colimit G

theorem profinite_spectrum_of_filtered_colimit
    {A : Type u} [CommRing A] (F : Type v) [Category.{v} F]
    [IsFiltered F] (G : F ⥤ CommRingCat)
    (hG : ∀ i, IsProfiniteSpace (PrimeSpectrum (G.obj i))) :
    IsProfiniteSpace (PrimeSpectrum (filteredColimitRing G)) := by
  sorry

/-! ## Localizing along a closed profinite subset -/

theorem exists_indZariski_wLocal_with_closed_points
    {A : Type u} [CommRing A] (I : Ideal A)
    (hV : IsProfiniteSpace {x : PrimeSpectrum A | ∀ a ∈ I, a ∈ x.asIdeal}) :
    ∃ B : CommRingCat, ∃ f : CommRingCat.of A ⟶ B,
      IsIndZariski f.hom ∧
        IsWLocalAffine (A := B) ∧
          closedPoints (PrimeSpectrum B) =
            {x : PrimeSpectrum B | ∀ a ∈ Ideal.map f.hom I, a ∈ x.asIdeal} ∧
            Nonempty (A ⧸ I ≃+* B ⧸ Ideal.map f.hom I) := by
  sorry

/-! ## Algebraic residue-field extensions over a w-local base -/

def wLocalClosedPointIdeal {A : Type u} [CommRing A]
    (hA : IsWLocalAffine (A := A)) : Ideal A :=
  PrimeSpectrum.vanishingIdeal (closedPoints (PrimeSpectrum A))

theorem wLocalClosedPointIdeal_isRadical
    {A : Type u} [CommRing A] (hA : IsWLocalAffine (A := A)) :
    (wLocalClosedPointIdeal hA).IsRadical := by
  sorry

theorem wLocalClosedPointIdeal_vanishing
    {A : Type u} [CommRing A] (hA : IsWLocalAffine (A := A)) :
    closedPoints (PrimeSpectrum A) =
      {x : PrimeSpectrum A |
        ∀ a ∈ wLocalClosedPointIdeal hA, a ∈ x.asIdeal} := by
  sorry

theorem wLocal_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsWLocalAffine (A := A)) (f : A →+* B)
    (hres : HasAlgebraicResidueExtensions f) :
    ({q : PrimeSpectrum B |
        ∀ a ∈ Ideal.map f (wLocalClosedPointIdeal hA), a ∈ q.asIdeal} ⊆
      closedPoints (PrimeSpectrum B)) ∧
      ∃ C : CommRingCat, ∃ g : CommRingCat.of B ⟶ C,
        IsIndZariski g.hom ∧
          Nonempty (B ⧸ Ideal.map f (wLocalClosedPointIdeal hA) ≃+*
            C ⧸ Ideal.map g.hom (Ideal.map f (wLocalClosedPointIdeal hA))) ∧
          IsWLocalAffine (A := C) ∧
          IsWLocalRingMap (g.hom.comp f) ∧
          PrimeSpectrum.comap (g.hom.comp f) ⁻¹'
              closedPoints (PrimeSpectrum A) =
            closedPoints (PrimeSpectrum C) := by
  sorry

end

end

end Formalization.Books.Proetale.Unit05
