import Formalization.Books.Algebra.Unit104.CohenMacaulayRings
import Formalization.Books.Algebra.Unit110.RegularRingsAndGlobalDimension
import Formalization.Books.Topology.Unit10.KrullDimension
import Formalization.Books.Topology.Unit11.CodimensionAndCatenary
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Topology.Clopen

/-!
# Commutative Algebra, Chapter 114: Dimension of finite type algebras over fields

The polynomial algebra in `n` variables is represented by
`MvPolynomial (Fin n) k`.  Krull dimensions use Mathlib's `ringKrullDim`,
prime heights use `Ideal.height`, and local dimensions of spectra use the
topological `krullDimensionAt` from Topology, Chapter 10.
-/

namespace Formalization.Books.Algebra.Unit114

universe u v

noncomputable section

open Set
open TopologicalSpace
open Formalization.Books.Topology.Unit10
open Formalization.Books.Topology.Unit11

/-! ## Local dimensions and components -/

/- The source's maximum over irreducible components through a point is the
   set of their canonical topological Krull dimensions. -/
def componentDimensionsAtPoint
    {X : Type u} [TopologicalSpace X] (x : X) : Set (WithBot ℕ∞) :=
  {d | ∃ Z : Set X,
    Z ∈ irreducibleComponents X ∧ x ∈ Z ∧ topologicalKrullDim Z = d}

/- The source's minimum over maximal localizations above a prime is recorded
   using the canonical maximal spectrum and localization at that ideal. -/
def maximalLocalDimensionsAbove
    {S : Type u} [CommRing S] (p : PrimeSpectrum S) : Set (WithBot ℕ∞) :=
  {d | ∃ m : MaximalSpectrum S,
    p.asIdeal ≤ m.asIdeal ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = d}

private lemma isIrreducible_preimage_of_isInducing
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : _root_.Topology.IsInducing f) {s : Set X}
    (hs : IsIrreducible s) (hsrange : s ⊆ Set.range f) :
    IsIrreducible (f ⁻¹' s) := by
  refine ⟨?_, ?_⟩
  · rcases hs.nonempty with ⟨x, hx⟩
    rcases hsrange hx with ⟨y, rfl⟩
    exact ⟨y, hx⟩
  · intro u v hu hv hU hV
    rcases hf.isOpen_iff.mp hu with ⟨u', huopen, hu_eq⟩
    rcases hf.isOpen_iff.mp hv with ⟨v', hvopen, hv_eq⟩
    have hsu : (s ∩ u').Nonempty := by
      rw [← hu_eq] at hU
      rcases hU with ⟨y, hyS, hyU⟩
      exact ⟨f y, hyS, hyU⟩
    have hsv : (s ∩ v').Nonempty := by
      rw [← hv_eq] at hV
      rcases hV with ⟨y, hyS, hyV⟩
      exact ⟨f y, hyS, hyV⟩
    rcases hs.2 u' v' huopen hvopen hsu hsv with ⟨x, hxs, hxu, hxv⟩
    rcases hsrange hxs with ⟨y, rfl⟩
    refine ⟨y, hxs, ?_⟩
    constructor
    · rw [← hu_eq]
      exact hxu
    · rw [← hv_eq]
      exact hxv

private theorem topologicalKrullDim_le_iSup_componentDimensions
    {X : Type u} [TopologicalSpace X] :
    topologicalKrullDim X ≤
      ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun A => ?_
  obtain ⟨Z, hZ, hAZ⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible
      (A : Set X) A.isIrreducible
  have hZnebot : topologicalKrullDim (Z : Set X) ≠ ⊥ := by
    rw [topologicalKrullDim, Order.krullDim_ne_bot_iff]
    let U : IrreducibleCloseds Z :=
      { carrier := Set.univ
        isIrreducible' :=
          @IrreducibleSpace.isIrreducible_univ Z _ (Subtype.irreducibleSpace hZ.1)
        isClosed' := isClosed_univ }
    exact ⟨U⟩
  have hheight : Order.height A ≤ topologicalKrullDim (Z : Set X) := by
    rw [← WithBot.le_unbotD_iff (a := 0) hZnebot]
    apply Order.height_le
    intro C hC
    let f : Z → X := (↑)
    have hf : _root_.Topology.IsClosedEmbedding f :=
      (isClosed_of_mem_irreducibleComponents Z hZ).isClosedEmbedding_subtypeVal
    let g : {V : IrreducibleCloseds X // (V : Set X) ⊆ Z} →
        IrreducibleCloseds Z := fun V =>
      { carrier := f ⁻¹' (V : Set X)
        isIrreducible' :=
          isIrreducible_preimage_of_isInducing hf.isInducing V.1.isIrreducible
            (fun x hx => ⟨⟨x, V.2 hx⟩, rfl⟩)
        isClosed' := V.1.isClosed.preimage hf.continuous }
    have hg : StrictMono g := by
      intro V W hVW
      apply lt_of_le_of_ne
      · change f ⁻¹' (V : Set X) ⊆ f ⁻¹' (W : Set X)
        exact Set.preimage_mono hVW.le
      · intro hEq
        apply hVW.2
        intro x hx
        have hxZ : x ∈ Z := W.2 hx
        have hx' : (⟨x, hxZ⟩ : Z) ∈ (g W : Set Z) := by
          exact hx
        have hx'' : (⟨x, hxZ⟩ : Z) ∈ (g V : Set Z) := by
          rw [hEq]
          exact hx'
        exact hx''
    have hsubset : ∀ i : Fin (C.length + 1),
        ((C i : IrreducibleCloseds X) : Set X) ⊆ Z := by
      intro i x hx
      have hi : (C i : Set X) ⊆ (C.last : Set X) :=
        C.monotone (Fin.le_last _)
      apply hAZ
      rw [← hC]
      exact hi hx
    let D : LTSeries (IrreducibleCloseds Z) :=
      { length := C.length
        toFun := fun i => g ⟨C i, hsubset i⟩
        step := fun i => hg (C.step i) }
    rw [WithBot.le_unbotD_iff (a := 0) hZnebot]
    simpa [D, topologicalKrullDim] using
      (Order.LTSeries.length_le_krullDim D)
  exact hheight.trans (le_iSup (fun Z : irreducibleComponents X =>
    topologicalKrullDim (Z : Set X)) ⟨Z, hZ⟩)

/-! ## The dimension of affine space -/

/-- A maximal ideal of affine `n`-space has `n` generators and its local ring
has dimension `n` and is regular local. -/
theorem dim_affine_space
    {k : Type u} [Field k] (n : ℕ)
    (m : MaximalSpectrum (MvPolynomial (Fin n) k)) :
    (∃ x : Fin n → MvPolynomial (Fin n) k,
        Ideal.span (Set.range x) = m.asIdeal) ∧
      ringKrullDim (Localization.AtPrime m.asIdeal) = n ∧
        IsRegularLocalRing (Localization.AtPrime m.asIdeal) := by
  sorry

/-- A polynomial algebra over a field is regular of global dimension `n`, and
all of its maximal localizations are regular local rings of dimension `n`. -/
theorem finite_gl_dim_polynomial_ring
    {k : Type u} [Field k] (n : ℕ) :
    Formalization.Books.Algebra.Unit110.IsRegularRing
        (MvPolynomial (Fin n) k) ∧
      Formalization.Books.Algebra.Unit109.globalDimension
          (MvPolynomial (Fin n) k) =
        ((n : ℕ∞) : WithBot ℕ∞) ∧
        ∀ m : MaximalSpectrum (MvPolynomial (Fin n) k),
          IsRegularLocalRing (Localization.AtPrime m.asIdeal) ∧
            ringKrullDim (Localization.AtPrime m.asIdeal) =
              ((n : ℕ∞) : WithBot ℕ∞) := by
  sorry

/-! ## Heights and chains in a polynomial algebra -/

/-- In a polynomial algebra over a field, every maximal prime chain between
two primes has length equal to the difference of their heights. -/
theorem dimension_height_polynomial_ring
    {k : Type u} [Field k] {n : ℕ}
    (p q : Ideal (MvPolynomial (Fin n) k))
    (hp : p.IsPrime) (hq : q.IsPrime) (hpq : p < q) :
    ∀ C : LTSeries
        (Set.Iic (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))),
      IsMaximalChainBetween
          (⟨p, hp⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (⟨q, hq⟩ : PrimeSpectrum (MvPolynomial (Fin n) k))
          (le_of_lt hpq) C →
        (C.length : ℕ∞) = q.height - p.height := by
  sorry

/-! ## Finite type domains and local dimensions -/

/-- The dimension of a finite-type domain over a field is the dimension of any
of its localizations at maximal ideals. -/
theorem dimension_spell_it_out
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [IsDomain S]
    (m : MaximalSpectrum S) :
    ringKrullDim S = ringKrullDim (Localization.AtPrime m.asIdeal) := by
  sorry

/-- At a point of the spectrum of a finite-type algebra over a field, the
topological local dimension is the maximum component dimension through the
point and the minimum dimension of a maximal localization above it. -/
theorem dimension_at_a_point_finite_type_over_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (p : Ideal S) (hp : p.IsPrime) :
    let x : PrimeSpectrum S := ⟨p, hp⟩
    ∃ d : WithBot ℕ∞,
      krullDimensionAt x = d ∧
        IsGreatest (componentDimensionsAtPoint x) d ∧
          IsLeast (maximalLocalDimensionsAbove x) d := by
  sorry

/-- A maximal ideal containing every minimal prime sees the global dimension. -/
theorem ringKrullDim_eq_krullDimensionAt_of_minimalPrimes_le
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : MaximalSpectrum S)
    (hmin : ∀ p : Ideal S, p ∈ minimalPrimes S → p ≤ m.asIdeal) :
    ringKrullDim S = krullDimensionAt (MaximalSpectrum.toPrimeSpectrum m) := by
  have hpoint :=
    dimension_at_a_point_finite_type_over_field (k := k) (S := S) m.asIdeal m.2.isPrime
  dsimp at hpoint
  obtain ⟨d, hdx, hdcomp, _⟩ := hpoint
  have hcomp : ∀ Z : Set (PrimeSpectrum S),
      Z ∈ irreducibleComponents (PrimeSpectrum S) →
        MaximalSpectrum.toPrimeSpectrum m ∈ Z := by
    intro Z hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZ
    rcases (Set.mem_image _ _ _).mp hZ with ⟨p, hp, rfl⟩
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (hmin p hp)
  have hdim : topologicalKrullDim (PrimeSpectrum S) ≤ d := by
    refine topologicalKrullDim_le_iSup_componentDimensions.trans ?_
    refine iSup_le fun Z => ?_
    exact hdcomp.2 ⟨Z, Z.2, hcomp Z Z.2, rfl⟩
  have hdim_lower : d ≤ ringKrullDim S := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    rcases hdcomp.1 with ⟨Z, hZ, _, hZd⟩
    rw [← hZd]
    exact topologicalKrullDim_subspace_le (PrimeSpectrum S) Z
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at hdim
  have hglobal : ringKrullDim S = d := le_antisymm hdim hdim_lower
  exact hglobal.trans hdx.symm

/-- The local dimension at a closed point of a finite-type affine algebra over
a field is the dimension of the corresponding maximal localization. -/
theorem dimension_closed_point_finite_type_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (m : MaximalSpectrum S) :
    krullDimensionAt (MaximalSpectrum.toPrimeSpectrum m) =
      ringKrullDim (Localization.AtPrime m.asIdeal) := by
  sorry

/-! ## Cohen--Macaulay finite-type algebras -/

/- The first form of the final lemma indexes the source's `T₀, ..., T_d`
   by the finite type `Fin (d + 1)`. The empty-spectrum case is included
   separately, matching the source's convention that the empty space has
   dimension `-∞`. -/
def HasDisjointEquidimensionalDecomposition
    (S : Type u) [CommRing S] : Prop :=
  IsEmpty (PrimeSpectrum S) ∨
    (∃ d : ℕ, ringKrullDim S = d ∧
      ∃ T : Fin (d + 1) → Set (PrimeSpectrum S),
        (∀ i, IsClopen (T i) ∧
          ∀ C ∈ irreducibleComponents (T i),
            topologicalKrullDim C = (i.1 : WithBot ℕ∞)) ∧
          (⋃ i, T i) = (Set.univ : Set (PrimeSpectrum S)) ∧
            (∀ i j, i ≠ j → Disjoint (T i) (T j)))

/- The equivalent product form of the source's decomposition.  The explicit
   family of commutative-ring structures keeps the product factors usable as
   ordinary Lean types. -/
def HasDimensionProductDecomposition
    (S : Type u) [CommRing S] : Prop :=
  IsEmpty (PrimeSpectrum S) ∨
    (∃ d : ℕ, ringKrullDim S = d ∧
      ∃ (R : Fin (d + 1) → Type u) (hR : ∀ i, CommRing (R i)),
        letI : ∀ i, CommRing (R i) := hR
        Nonempty (S ≃+* (∀ i, R i)) ∧
          ∀ i : Fin (d + 1),
            ∀ m : MaximalSpectrum (R i),
              m.asIdeal.height = (i.1 : ℕ∞))

/-- A finite-type Cohen--Macaulay algebra over a field decomposes
into open and closed equidimensional pieces, equivalently into ring factors
whose maximal ideals have the corresponding heights. -/
theorem disjoint_decomposition_CM_algebra
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S]
    (hS :
      letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
      Formalization.Books.Algebra.Unit104.IsCohenMacaulayRing S) :
    HasDisjointEquidimensionalDecomposition S ∧
      (HasDisjointEquidimensionalDecomposition S ↔
        HasDimensionProductDecomposition S) := by
  sorry

end

end Formalization.Books.Algebra.Unit114
