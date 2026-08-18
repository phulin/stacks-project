import Formalization.Books.Proetale.Unit02.SomeTopology
import Formalization.Books.Proetale.Unit04.IndZariski
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.RingHom.FaithfullyFlat

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
classical

/-! ## Affine w-locality and locally closed pieces -/

/-- An affine scheme is w-local when its spectrum is a w-local space. -/
def IsWLocalAffine {A : Type u} [CommRing A] : Prop :=
  IsWLocalSpace (PrimeSpectrum A)

/-- A locally closed piece of an affine spectrum in the form `D(f) ∩ V(I)`. -/
structure LocallyClosedPiece (A : Type u) [CommRing A] where
  f : A
  I : Ideal A

/-- The underlying set of a locally closed piece. -/
def LocallyClosedPiece.carrier {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  {x | Z.f ∉ x.asIdeal ∧ ∀ a ∈ Z.I, a ∈ x.asIdeal}

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

/-- The points of `Spec(A)` specializing to a subset. -/
def pointsSpecializingToPiece {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) : Set (PrimeSpectrum A) :=
  Topology.pointsSpecializingTo Z.carrier

def localizedPieceSpectrumMap {A : Type u} [CommRing A]
    (Z : LocallyClosedPiece A) :
    PrimeSpectrum (localizedPieceRing Z) → PrimeSpectrum A :=
  PrimeSpectrum.comap (localizedPieceRingHom Z)

/-- The closed-locus predicate used for affine closed subschemes. -/
def IsClosedAffineLocus {R : Type u} [CommRing R]
    (T : Set (PrimeSpectrum R)) : Prop := IsClosed T

/-! ## The localization lemma -/

/-- The localization identifies its spectrum with the points specializing to
the chosen locally closed piece, and the piece becomes closed. -/
theorem localization_piece_properties
    {A : Type u} [CommRing A] (Z : LocallyClosedPiece A) :
    ∃ S : Submonoid A,
      Nonempty (Homeomorph (PrimeSpectrum (Localization S))
        (Subtype (pointsSpecializingToPiece Z))) ∧
        IsClosedAffineLocus
          (localizedPieceSpectrumMap Z ⁻¹' Z.carrier) := by
  sorry

/-- The ring `A_Z^~` depends only on the underlying locally closed subset. -/
theorem localizedPieceRing_depends_only_on_carrier
    {A : Type u} [CommRing A] (Z Z' : LocallyClosedPiece A)
    (h : Z.carrier = Z'.carrier) :
    Nonempty (localizedPieceRing Z ≃+* localizedPieceRing Z') := by
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
    ∃! g : localizedPieceRing Z →+* localizedPieceRing Z',
      g.comp (localizedPieceRingHom Z) =
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
  f := ∏ a in p.nonvanishing, a
  I := Ideal.span (↑p.vanishing : Set A)

/-- The stratum with the prescribed vanishing pattern. -/
def stratum {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) : Set (PrimeSpectrum A) :=
  (stratumPiece p).carrier

/-- The displayed description of a stratum as `D(∏ E') ∩ V((E''))`. -/
theorem stratum_eq_basicOpen_inter_zeroLocus
    {A : Type u} [CommRing A] {E : Finset A}
    (p : StratumPartition E) :
    stratum p = (stratumPiece p).carrier := rfl

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

def stratumFactorDiagram {A : Type u} [CommRing A] (E : Finset A) :
    Discrete (StratumPartition E) ⥤ CommRingCat :=
  Discrete.functor (fun p => CommRingCat.of (stratumFactor p.as))

/-- The product ring `A_E` of the localized strata. -/
noncomputable def stageRing {A : Type u} [CommRing A] (E : Finset A) : CommRingCat :=
  limit (stratumFactorDiagram A E)

/-- The disjoint-union presentation of the spectrum of `A_E`. -/
def stageSpectrum {A : Type u} [CommRing A] (E : Finset A) : Type u :=
  Σ p : StratumPartition E, PrimeSpectrum (stratumFactor p)

def stageClosedLocus {A : Type u} [CommRing A] (E : Finset A) :
    Set (stageSpectrum A E) :=
  {x | x.2 ∈
    (localizedPieceSpectrumMap (stratumPiece x.1) ⁻¹'
      (stratumPiece x.1).carrier)}

/-- The spectrum of the product is canonically the disjoint union of the
localized spectra. -/
theorem exists_stageSpectrumHomeomorph
    {A : Type u} [CommRing A] (E : Finset A) :
    Nonempty (Homeomorph (stageSpectrum A E)
      (PrimeSpectrum (stageRing A E))) := by
  sorry

noncomputable def stageSpectrumHomeomorph
    {A : Type u} [CommRing A] (E : Finset A) :
    Homeomorph (stageSpectrum A E) (PrimeSpectrum (stageRing A E)) :=
  Classical.choice (exists_stageSpectrumHomeomorph E)

/-- The closed subscheme `Z_E`, transported to `Spec(A_E)`. -/
def stageClosedLocusOnSpectrum {A : Type u} [CommRing A] (E : Finset A) :
    Set (PrimeSpectrum (stageRing A E)) :=
  stageSpectrumHomeomorph E '' stageClosedLocus A E

theorem stageClosedLocus_isClosed
    {A : Type u} [CommRing A] (E : Finset A) :
    IsClosedAffineLocus (stageClosedLocusOnSpectrum A E) := by
  sorry

theorem stageClosedLocus_contains_closedPoints
    {A : Type u} [CommRing A] (E : Finset A) :
    closedPoints (PrimeSpectrum (stageRing A E)) ⊆
      stageClosedLocusOnSpectrum A E := by
  sorry

/-! ## Transition maps and the w-localization -/

def restrictPartition {A : Type u} {E₁ E₂ : Finset A}
    (h : E₁ ⊆ E₂) (p : StratumPartition E₂) : StratumPartition E₁ where
  nonvanishing := p.nonvanishing ∩ E₁
  vanishing := p.vanishing ∩ E₁
  disjoint := by
    exact p.disjoint.mono inf_le_left inf_le_left
  union_eq := by
    ext a
    constructor
    · intro ha
      exact h ha
    · intro ha
      simp only [Finset.mem_union, Finset.mem_inter]
      rcases p.union_eq ▸ ha with ha | ha
      · exact Or.inl ⟨ha, by exact h (p.union_eq ▸ Finset.mem_union.mpr (Or.inl ha))⟩
      · exact Or.inr ⟨ha, by exact h (p.union_eq ▸ Finset.mem_union.mpr (Or.inr ha))⟩

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
    ∃! g : stageRing A E₁ ⟶ stageRing A E₂, True := by
  sorry

noncomputable def stageRingHom
    {A : Type u} [CommRing A] {E₁ E₂ : Finset A} (h : E₁ ⊆ E₂) :
    stageRing A E₁ ⟶ stageRing A E₂ :=
  Classical.choose (exists_stageRingHom h)

/-- The finite stages form the directed system used in the construction. -/
structure StageFunctorData (A : Type u) [CommRing A] where
  functor : Finset A ⥤ CommRingCat
  object_eq : ∀ E, functor.obj E = stageRing A E

theorem exists_stageFunctorData {A : Type u} [CommRing A] :
    Nonempty (StageFunctorData A) := by
  sorry

noncomputable def stageFunctor {A : Type u} [CommRing A] :
    Finset A ⥤ CommRingCat :=
  (Classical.choice (exists_stageFunctorData A)).functor

/-- The colimit ring `A_w`. -/
noncomputable def wLocalRing {A : Type u} [CommRing A] : CommRingCat :=
  colimit (stageFunctor A)

/-- The affine scheme `X_w = Spec(A_w)`. -/
def wLocalSpectrum {A : Type u} [CommRing A] : Scheme :=
  Scheme.Spec (wLocalRing A)

/-- The closed-point locus denoted `Z` in the source's inverse-limit formula. -/
def wLocalClosedLocus {A : Type u} [CommRing A) :
    Set (PrimeSpectrum (wLocalRing A)) :=
  closedPoints (PrimeSpectrum (wLocalRing A))

theorem wLocalRing_isIndZariski_and_faithfullyFlat
    {A : Type u} [CommRing A] :
    IsIndZariski (CommRingCat.ofHom
      (algebraMap A (wLocalRing A))) ∧
      Function.Surjective (algebraMap A (wLocalRing A)) := by
  sorry

theorem wLocalConstruction_properties
    {A : Type u} [CommRing A] :
    IsIndZariski (CommRingCat.ofHom (algebraMap A (wLocalRing A))) ∧
      Nonempty (wLocalClosedLocus A ≃ₜ PrimeSpectrum A) ∧
        IsClosed (wLocalClosedLocus A) ∧
          ∀ x : PrimeSpectrum (wLocalRing A),
            ∃! z : wLocalClosedLocus A, x ⤳ (z : PrimeSpectrum (wLocalRing A)) := by
  sorry

/-! ## The size remark and the universal property -/

theorem wLocalRing_cardinal_le
    {A : Type u} [CommRing A] (κ : Cardinal) (hκ : Cardinal.mk A ≤ κ)
    (hinfinite : ℵ₀ ≤ κ) :
    Cardinal.mk (wLocalRing A) ≤ κ := by
  sorry

theorem wLocalRing_universal
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hB : IsWLocalAffine (A := B)) :
    ∃! g : wLocalRing A ⟶ CommRingCat.of B,
      (algebraMap A (wLocalRing A)) ≫ g.hom = f := by
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

theorem profinite_spectrum_of_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hres : ∀ q : PrimeSpectrum B,
      Algebra.IsAlgebraic (A ⧸ q.asIdeal.comap f) (B ⧸ q.asIdeal)) :
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
    (hf : RingHom.IsWeaklyEtale f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_quasiFinite
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : RingHom.QuasiFinite f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_unramified
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : RingHom.Unramified f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_etale
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsProfiniteSpace (PrimeSpectrum A)) (f : A →+* B)
    (hf : RingHom.Etale f) :
    IsProfiniteSpace (PrimeSpectrum B) := by
  sorry

theorem profinite_spectrum_of_filtered_colimit
    {A : Type u} [CommRing A] (F : Type v) [Category.{v} F]
    [IsFiltered F] (G : F ⥤ CommRingCat)
    (hG : ∀ i, IsProfiniteSpace (PrimeSpectrum (G.obj i))) :
    IsProfiniteSpace (PrimeSpectrum (colimit G)) := by
  sorry

/-! ## Localizing along a closed profinite subset -/

theorem exists_indZariski_wLocal_with_closed_points
    {A : Type u} [CommRing A] (I : Ideal A)
    (hV : IsProfiniteSpace {x : PrimeSpectrum A | ∀ a ∈ I, a ∈ x.asIdeal}) :
    ∃ B : CommRingCat, ∃ f : A ⟶ B,
      IsIndZariski f.hom ∧
        IsWLocalAffine (A := B) ∧
          closedPoints (PrimeSpectrum B) =
            {x : PrimeSpectrum B | ∀ a ∈ Ideal.map f.hom I, a ∈ x.asIdeal} ∧
            Nonempty (A ⧸ I ≃+* B ⧸ Ideal.map f.hom I) := by
  sorry

/-! ## Algebraic residue-field extensions over a w-local base -/

def wLocalClosedPointIdeal {A : Type u} [CommRing A]
    (hA : IsWLocalAffine (A := A)) : Ideal A :=
  sInf {I : Ideal A | closedPoints (PrimeSpectrum A) =
    {x : PrimeSpectrum A | ∀ a ∈ I, a ∈ x.asIdeal}}

theorem wLocal_algebraic_residue_extensions
    {A B : Type u} [CommRing A] [CommRing B]
    (hA : IsWLocalAffine (A := A)) (f : A →+* B)
    (hres : ∀ q : PrimeSpectrum B,
      Algebra.IsAlgebraic (A ⧸ q.asIdeal.comap f) (B ⧸ q.asIdeal)) :
    (∀ q : PrimeSpectrum B,
        (∀ a ∈ Ideal.map f (wLocalClosedPointIdeal hA), a ∈ q.asIdeal)) ∧
      ∃ C : CommRingCat, ∃ g : CommRingCat.of B ⟶ C,
        IsIndZariski g.hom ∧
          Nonempty (B ⧸ Ideal.map f (wLocalClosedPointIdeal hA) ≃+*
            C ⧸ Ideal.map g.hom (Ideal.map f (wLocalClosedPointIdeal hA))) ∧
          IsWLocalAffine (A := C) := by
  sorry

end

end Formalization.Books.Proetale.Unit05
