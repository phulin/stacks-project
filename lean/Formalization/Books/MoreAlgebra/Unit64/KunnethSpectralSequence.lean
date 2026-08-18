import Formalization.Books.MoreAlgebra.Unit59.DerivedTensorProduct
import Formalization.Books.Homology.Unit24.FilteredComplexes
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# More on Algebra, Chapter 64: Künneth spectral sequence

The filtered-complex and spectral-sequence interfaces are those of Homology,
Chapter 24.  This file records the tensor-product filtration, its flatness
and convergence hypotheses, the filtered free resolution statement, and the
bounded Künneth spectral sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Derived.Unit08
open Formalization.Books.Derived.Unit11
open Formalization.Books.Homology.Unit19
open Formalization.Books.Homology.Unit20
open Formalization.Books.Homology.Unit24
open Formalization.Books.MoreAlgebra.Unit56
open Formalization.Books.MoreAlgebra.Unit58
open Formalization.Books.MoreAlgebra.Unit59
open scoped BigOperators

universe w u

namespace Formalization.Books.MoreAlgebra.Unit64

/-! ## Complexes, filtrations, and the tensor product -/

/-- The category of `R`-modules used throughout the chapter. -/
abbrev Mod (R : Type u) [CommRing R] := ModuleCat.{u} R

/-- Integer-indexed cochain complexes of `R`-modules. -/
abbrev Comp (R : Type u) [CommRing R] := Unit59.Comp R

/-- Filtered integer-indexed cochain complexes of `R`-modules. -/
abbrev FilteredComp (R : Type u) [CommRing R] :=
  Unit24.FilteredComplex (Mod R)

/-- The unfiltered complex underlying a filtered complex. -/
noncomputable abbrev forgetFiltered (K : FilteredComp R) : Comp R :=
  Unit24.filteredComplexUnderlying K

/-- The ordinary total tensor product underlying the filtered tensor product. -/
noncomputable abbrev tensorUnderlying
    (K L : FilteredComp R) : Comp R :=
  Unit59.tensorProductComplex R (forgetFiltered K) (forgetFiltered L)

/-- The map from a tensor product of two filtration steps into the corresponding
summand of the total tensor product. -/
noncomputable def tensorFiltrationSummandMap
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (n p i : ℤ) (h : i + (n - i) = n) :
    ((K.X i).filtration.obj p : Mod R) ⊗
        ((L.X (n - i)).filtration.obj (p - i) : Mod R) ⟶
      (tensorUnderlying K L).X n :=
  ((K.X i).filtration.obj p).arrow ⊗ₘ
        ((L.X (n - i)).filtration.obj (p - i)).arrow ≫
      Unit58.ιMapBifunctor (forgetFiltered K) (forgetFiltered L)
        (MonoidalCategory.curriedTensor (Mod R)) (.up ℤ) i (n - i) n h

/-- The image subobject contributed by the summand with cochain degree `i`.
The supremum over all `i` is the source's direct sum filtration. -/
noncomputable def tensorFiltrationSummand
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (n p i : ℤ) : Subobject ((tensorUnderlying K L).X n) :=
  Subobject.mk (Abelian.image.ι (tensorFiltrationSummandMap K L n p i (by omega)))

/-- The `p`th step of the decreasing filtration on the total tensor product. -/
noncomputable def tensorFiltrationStep
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (n p : ℤ) : Subobject ((tensorUnderlying K L).X n) :=
  sSup (Set.range (tensorFiltrationSummand K L n p))

/-- The direct-sum formula for the tensor-product filtration. -/
def TensorFiltrationFormula
    {R : Type u} [CommRing R] (T : FilteredComp R)
    (K L : FilteredComp R) : Prop :=
  ∀ n p : ℤ,
    (T.X n).filtration.obj p = tensorFiltrationStep K L n p

/-- A filtered total tensor product together with the source's filtration
formula.  The underlying-complex isomorphism makes the construction usable
even when a chosen categorical representative is used. -/
structure TensorFilteredComplexData
    {R : Type u} [CommRing R] (K L : FilteredComp R) where
  complex : FilteredComp R
  underlyingIso : Nonempty (forgetFiltered complex ≅ tensorUnderlying K L)
  filtration_formula : TensorFiltrationFormula complex K L

/-- The tensor-product filtration exists as a filtered complex. -/
theorem tensorFilteredComplexData_exists
    {R : Type u} [CommRing R] (K L : FilteredComp R) :
    Nonempty (TensorFilteredComplexData K L) := by
  sorry

/-- A chosen filtered total tensor product. -/
noncomputable def tensorFilteredComplex
    {R : Type u} [CommRing R] (K L : FilteredComp R) : FilteredComp R :=
  (Classical.choice (tensorFilteredComplexData_exists K L)).complex

/-- The chosen tensor filtration has the source's direct-sum formula. -/
theorem tensorFilteredComplex_filtration_formula
    {R : Type u} [CommRing R] (K L : FilteredComp R) :
    TensorFiltrationFormula (tensorFilteredComplex K L) K L := by
  exact (Classical.choice (tensorFilteredComplexData_exists K L)).filtration_formula

/-- The chosen filtered tensor product represents the ordinary total tensor
product. -/
theorem tensorFilteredComplex_underlying_iso
    {R : Type u} [CommRing R] (K L : FilteredComp R) :
    Nonempty (forgetFiltered (tensorFilteredComplex K L) ≅ tensorUnderlying K L) := by
  exact (Classical.choice (tensorFilteredComplexData_exists K L)).underlyingIso

/-- Termwise flatness of a filtered complex, including its filtration steps and
associated graded pieces. -/
def FilteredComplexFlat
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  (∀ n : ℤ, Module.Flat R ((K.X n).carrier : Type u)) ∧
    (∀ n p : ℤ, Module.Flat R ((K.X n).filtration.obj p : Type u)) ∧
    (∀ n p : ℤ, Module.Flat R (gradedPiece (K.X n) p : Type u))

/-- The flatness assumptions used for the tensor-product filtration. -/
def TensorProductFlat
    {R : Type u} [CommRing R] (K L : FilteredComp R) : Prop :=
  FilteredComplexFlat K ∧ FilteredComplexFlat L

/-- The associated-graded tensor-product summand. -/
noncomputable abbrev gradedTensorSummand
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (i j : ℤ) : Comp R :=
  tensorProductComplex R
    (Unit24.filteredComplexUnshiftedGradedPiece K i)
    (Unit24.filteredComplexUnshiftedGradedPiece L j)

/-- The direct sum of the graded tensor-product summands with `i + j = n`. -/
noncomputable abbrev gradedTensorSum
    {R : Type u} [CommRing R] (K L : FilteredComp R) (n : ℤ) : Comp R :=
  ∐ fun i : ℤ => gradedTensorSummand K L i (n - i)

/-- The short exact sequence expressing `grⁿ(T)` as the direct sum of the
graded tensor-product complexes. -/
structure TensorProductFiltrationSequence
    {R : Type u} [CommRing R] (K L : FilteredComp R) (n : ℤ) where
  projection : Unit20.filteredComplexStepComplex (tensorFilteredComplex K L) n ⟶
    gradedTensorSum K L n
  projection_zero :
    Unit20.filteredComplexStepInclusion (tensorFilteredComplex K L) n (n + 1) (by omega) ≫
        projection = 0
  exact :
    (ShortComplex.mk
      (Unit20.filteredComplexStepInclusion
        (tensorFilteredComplex K L) n (n + 1) (by omega))
      projection projection_zero).ShortExact

/-- Under the termwise flatness hypotheses, the tensor-product filtration has
the source's short exact graded-piece sequence. -/
theorem tensorProduct_filtration_sequence_exists
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) (n : ℤ) :
    Nonempty (TensorProductFiltrationSequence K L n) := by
  sorry

/-- The direct sum decomposition of the associated graded tensor product. -/
theorem tensorProduct_associatedGraded_sum
    {R : Type u} [CommRing R] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) (n : ℤ) :
    Nonempty
      (gradedTensorSum K L n ≅
        Unit24.filteredComplexGradedPiece (tensorFilteredComplex K L) n) := by
  sorry

/-! ## The `E₁` page and its differential -/

/-- The cohomology of the derived tensor product of two associated-graded
complexes. -/
noncomputable abbrev derivedGradedTensorCohomology
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (i j n : ℤ) : Mod R :=
  (derivedCohomologyFunctor (Mod R) n).obj
    (derivedTensor
      ((derivedComplexQuotient R).obj
        (Unit24.filteredComplexUnshiftedGradedPiece K i))
      ((derivedComplexQuotient R).obj
        (Unit24.filteredComplexUnshiftedGradedPiece L j)))

/-- The source's direct-sum formula for the `E₁` term. -/
noncomputable abbrev kunnethE₁Term
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (p q : ℤ) : Mod R :=
  ∐ fun i : ℤ => derivedGradedTensorCohomology K L i (p - i) (p + q)

/-- The two associated-graded summands receiving a `d₁` from the `(i,j)`
summand. -/
noncomputable abbrev kunnethD₁Target
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (p q i j : ℤ) : Mod R :=
  derivedGradedTensorCohomology K L (i + 1) j (p + q + 1) ⊞
    derivedGradedTensorCohomology K L i (j + 1) (p + q + 1)

/-- The canonical map from the two `d₁` target summands into the next direct
sum page. -/
noncomputable def kunnethD₁TargetInclusion
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (p q i j : ℤ) (hij : i + j = p) :
    kunnethD₁Target K L p q i j ⟶ kunnethE₁Term K L (p + 1) q := by
  apply biprod.desc
  · exact eqToHom (by congr 2 <;> omega) ≫
      Sigma.ι (fun a : ℤ => derivedGradedTensorCohomology K L a (p + 1 - a)
        (p + q + 1)) (i + 1)
  · exact eqToHom (by congr 2 <;> omega) ≫
      Sigma.ι (fun a : ℤ => derivedGradedTensorCohomology K L a (p + 1 - a)
        (p + q + 1)) i

/-- A precise factorization statement for the source's description of `d₁`:
the differential on the `(i,j)` summand factors through the two summands
`(i+1,j)` and `(i,j+1)`. -/
def KunnethD₁Support
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (p q : ℤ) (d : kunnethE₁Term K L p q ⟶ kunnethE₁Term K L (p + 1) q) : Prop :=
  ∀ i j : ℤ, ∀ hij : i + j = p,
    ∃ f : derivedGradedTensorCohomology K L i j (p + q) ⟶
        kunnethD₁Target K L p q i j,
      f ≫ kunnethD₁TargetInclusion K L p q i j hij =
        eqToHom (by congr 2 <;> omega) ≫
          Sigma.ι (fun a : ℤ => derivedGradedTensorCohomology K L a (p - a)
            (p + q)) i ≫ d

/-! ## Convergence and the filtered-complex spectral sequence -/

/-- The finite-filtration alternative in the convergence lemma. -/
def KunnethFiniteFiltration
    {R : Type u} [CommRing R] (K L : FilteredComp R) : Prop :=
  Unit24.FilteredComplexFiniteFiltration K ∧
    Unit24.FilteredComplexFiniteFiltration L

/-- A filtration is eventually acyclic above. -/
def KunnethAcyclicAbove
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  ∃ b : ℤ, ∀ i : ℤ, b ≤ i →
    IsAcyclic (Unit24.filteredComplexFiltrationStep K i)

/-- A sufficiently negative filtration step is quasi-isomorphic to the whole
complex. -/
def KunnethQuasiIsoBelow
    {R : Type u} [CommRing R] (K : FilteredComp R) : Prop :=
  ∃ a : ℤ, ∀ i : ℤ, i ≤ a →
    QuasiIso (Unit20.filteredComplexStepToUnderlying K i)

/-- The general convergence alternative for a pair of filtrations. -/
def KunnethEventualFiltration
    {R : Type u} [CommRing R] (K L : FilteredComp R) : Prop :=
  KunnethAcyclicAbove K ∧ KunnethQuasiIsoBelow K ∧
    KunnethAcyclicAbove L ∧ KunnethQuasiIsoBelow L

/-- The hypotheses of the filtered-complex convergence lemma. -/
def KunnethConvergenceHypotheses
    {R : Type u} [CommRing R] (K L : FilteredComp R) : Prop :=
  KunnethFiniteFiltration K L ∨ KunnethEventualFiltration K L

/-- Data for the filtered tensor-product spectral sequence. -/
structure KunnethFilteredSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R) where
  spectralSequence :
    Unit24.FilteredComplexSpectralSequence (tensorFilteredComplex K L)
  e₁_page : ∀ p q : ℤ,
    Nonempty (spectralSequence.page 1 (p, q) ≅ kunnethE₁Term K L p q)
  e₁_differential_support : ∀ (p q : ℤ),
    ∃ e : spectralSequence.page 1 (p, q) ≅ kunnethE₁Term K L p q,
      ∃ e' : spectralSequence.page 1 (p + 1, q) ≅ kunnethE₁Term K L (p + 1) q,
        KunnethD₁Support K L p q
          (e.hom ≫ spectralSequence.differential 1 (p, q) ≫
            eqToHom (by congr 1 <;> omega) ≫ e'.inv)
  convergence : KunnethConvergenceHypotheses K L →
    Unit24.filteredComplexConverges (tensorFilteredComplex K L)

/-- Existence of the filtered tensor-product spectral sequence under the flat
term hypotheses. -/
theorem kunneth_filtered_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) :
    Nonempty (KunnethFilteredSpectralSequenceData K L) := by
  sorry

/-- A chosen Künneth filtered spectral sequence. -/
noncomputable def kunnethFilteredSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) :
    KunnethFilteredSpectralSequenceData K L :=
  Classical.choice (kunneth_filtered_spectral_sequence_exists K L hflat)

/-- The chosen filtered tensor-product spectral sequence. -/
noncomputable abbrev kunnethFilteredSpectralSequence
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) :
    Unit24.FilteredComplexSpectralSequence (tensorFilteredComplex K L) :=
  (kunnethFilteredSpectralSequenceData K L hflat).spectralSequence

/-- Its source's `E₁` page. -/
theorem kunneth_filtered_spectral_sequence_e₁_page
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L) (p q : ℤ) :
    Nonempty ((kunnethFilteredSpectralSequence K L hflat).page 1 (p, q) ≅
      kunnethE₁Term K L p q) := by
  exact (kunnethFilteredSpectralSequenceData K L hflat).e₁_page p q

/-- The chosen spectral sequence converges whenever either source convergence
alternative holds. -/
theorem kunneth_filtered_spectral_sequence_converges
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)] (K L : FilteredComp R)
    (hflat : TensorProductFlat K L)
    (hconv : KunnethConvergenceHypotheses K L) :
    Unit24.filteredComplexConverges (tensorFilteredComplex K L) := by
  exact (kunnethFilteredSpectralSequenceData K L hflat).convergence hconv

/-! ## Filtered free resolutions -/

/- The following three maps forget the filtration on a filtered map, or apply
the map to a fixed filtration step or associated-graded piece.  They are the
complex-level versions of the three quasi-isomorphisms in the source. -/
noncomputable def filteredMapUnderlying
    {R : Type u} [CommRing R] {K L : FilteredComp R} (f : K ⟶ L) :
    forgetFiltered K ⟶ forgetFiltered L := by
  refine { f := fun n => (f.f n).hom, comm' := ?_ }
  intro n m hnm
  sorry

noncomputable def filteredStepMap
    {R : Type u} [CommRing R] {K L : FilteredComp R} (f : K ⟶ L) (p : ℤ) :
    Unit20.filteredComplexStepComplex K p ⟶
      Unit20.filteredComplexStepComplex L p := by
  refine { f := fun n => filtrationStepMap (f.f n) p, comm' := ?_ }
  intro n m hnm
  sorry

noncomputable def filteredGradedMap
    {R : Type u} [CommRing R] {K L : FilteredComp R} (f : K ⟶ L) (p : ℤ) :
    Unit24.filteredComplexUnshiftedGradedPiece K p ⟶
      Unit24.filteredComplexUnshiftedGradedPiece L p := by
  refine { f := fun n => gradedPieceMap (f.f n) p, comm' := ?_ }
  intro n m hnm
  sorry

/-- A filtered complex with free terms, free filtration steps, and free graded
pieces, all K-flat. -/
structure FilteredFreeKFlatResolution
    {R : Type u} [CommRing R] (K : FilteredComp R) where
  complex : FilteredComp R
  map : complex ⟶ K
  term_free : ∀ n : ℤ, Module.Free R ((complex.X n).carrier : Type u)
  filtration_free : ∀ n p : ℤ,
    Module.Free R ((complex.X n).filtration.obj p : Type u)
  graded_free : ∀ n p : ℤ,
    Module.Free R (gradedPiece (complex.X n) p : Type u)
  complex_kflat : IsKFlat (forgetFiltered complex)
  filtration_kflat : ∀ p : ℤ,
    IsKFlat (Unit24.filteredComplexFiltrationStep complex p)
  graded_kflat : ∀ p : ℤ,
    IsKFlat (Unit24.filteredComplexUnshiftedGradedPiece complex p)
  quasiIso : QuasiIso (filteredMapUnderlying map)
  filtration_quasiIso : ∀ p : ℤ,
    QuasiIso (filteredStepMap map p)
  graded_quasiIso : ∀ p : ℤ,
    QuasiIso (filteredGradedMap map p)

/-- Every filtered complex admits a filtered K-flat free resolution with the
termwise, filtration-step, and associated-graded quasi-isomorphisms stated in
the source. -/
theorem exists_filteredFreeKFlatResolution
    {R : Type u} [CommRing R] (K : FilteredComp R) :
    Nonempty (FilteredFreeKFlatResolution K) := by
  sorry

/-! ## The bounded Künneth spectral sequence -/

/-- Cohomology of a bounded derived object in degree `n`. -/
noncomputable abbrev boundedDerivedCohomology
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K : Unit56.DBounded R) (n : ℤ) : Mod R :=
  (derivedCohomologyFunctor (Mod R) n).obj
    ((DerivedCategory.Bounded.ι (C := Mod R)).obj K)

/-- The canonical derived tensor product of two bounded derived objects. -/
noncomputable abbrev boundedDerivedTensor
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) : Unit56.D R :=
  derivedTensor
    ((DerivedCategory.Bounded.ι (C := Mod R)).obj K)
    ((DerivedCategory.Bounded.ι (C := Mod R)).obj L)

/-- Cohomology of the derived tensor product of two bounded objects. -/
noncomputable abbrev boundedDerivedTensorCohomology
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) (n : ℤ) : Mod R :=
  (derivedCohomologyFunctor (Mod R) n).obj (boundedDerivedTensor K L)

/-- The `E₂`-cohomological spectral sequence with the source's bidegree.
The bidegree `(r,1-r)` is encoded by Mathlib's spectral-sequence shape. -/
abbrev BoundedKunnethSpectralSequence (R : Type u) [CommRing R] :=
  CategoryTheory.E₂CohomologicalSpectralSequence (Mod R)

/-- A convergence package for a bounded cohomological spectral sequence. -/
structure BoundedKunnethConvergence
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (E : BoundedKunnethSpectralSequence R)
    (K L : Unit56.DBounded R) where
  eInf : ℤ × ℤ → Mod R
  filtration : ∀ n : ℤ,
    DecreasingFiltration (Mod R) (boundedDerivedTensorCohomology K L n)
  filtration_finite : ∀ n : ℤ,
    (FilteredObject.mk (boundedDerivedTensorCohomology K L n) (filtration n)).IsFinite
  stabilizes : ∀ p q : ℤ, ∃ r₀ : ℤ, 2 ≤ r₀ ∧
    ∀ r : ℤ, r₀ ≤ r → Nonempty ((E.page r).X (p, q) ≅ eInf (p, q))
  abutment : ∀ p q : ℤ,
    Nonempty (eInf (p, q) ≅ gradedPiece
      (FilteredObject.mk (boundedDerivedTensorCohomology K L (p + q))
        (filtration (p + q))) p)

/-- Data for the bounded Künneth spectral sequence. -/
structure BoundedKunnethSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) where
  spectralSequence : BoundedKunnethSpectralSequence R
  e₂_page : ∀ p q : ℤ,
    Nonempty ((spectralSequence.page 2).X (p, q) ≅
      ∐ fun ij : {x : ℤ × ℤ // x.1 + x.2 = q} =>
        Formalization.Books.Algebra.Unit75.Tor
          (boundedDerivedCohomology K ij.1.1)
          (boundedDerivedCohomology L ij.1.2) (-p).toNat)
  convergence : BoundedKunnethConvergence spectralSequence K L

/-- Existence of the bounded Künneth spectral sequence. -/
theorem bounded_kunneth_spectral_sequence_exists
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) :
    Nonempty (BoundedKunnethSpectralSequenceData K L) := by
  sorry

/-- The chosen bounded Künneth spectral sequence. -/
noncomputable def boundedKunnethSpectralSequenceData
    {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) :
    BoundedKunnethSpectralSequenceData K L :=
  Classical.choice (bounded_kunneth_spectral_sequence_exists K L)

/-- The Dedekind-domain collapse and its universal-coefficient short exact
sequence. -/
structure DedekindKunnethShortExact
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) (n : ℤ) where
  sequence : ShortComplex (Mod R)
  exact : sequence.ShortExact
  left_iso : Nonempty (sequence.X₁ ≅
    ∐ fun ij : {x : ℤ × ℤ // x.1 + x.2 = n} =>
      boundedDerivedCohomology K ij.1.1 ⊗ boundedDerivedCohomology L ij.1.2)
  middle_iso : Nonempty (sequence.X₂ ≅
    (derivedCohomologyFunctor (Mod R) n).obj (boundedDerivedTensor K L))
  right_iso : Nonempty (sequence.X₃ ≅
    ∐ fun ij : {x : ℤ × ℤ // x.1 + x.2 = n + 1} =>
      Formalization.Books.Algebra.Unit75.Tor
        (boundedDerivedCohomology K ij.1.1)
        (boundedDerivedCohomology L ij.1.2) 1)

/-- For `R = ℤ` or a Dedekind domain, `Tor_i` vanishes for `i > 1`, so the
bounded Künneth spectral sequence yields the source's short exact sequence. -/
theorem kunneth_dedekind_shortExact
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    [HasDerivedCategory.{w} (Mod R)]
    (K L : Unit56.DBounded R) (n : ℤ) :
    Nonempty (DedekindKunnethShortExact K L n) := by
  sorry

end Formalization.Books.MoreAlgebra.Unit64
