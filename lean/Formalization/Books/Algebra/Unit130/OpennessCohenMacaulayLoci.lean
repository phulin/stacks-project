import Formalization.Books.Algebra.Unit125.DimensionOfFibres
import Formalization.Books.Algebra.Unit129.OpennessFlatLocus
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite

/-!
# Commutative Algebra, Chapter 130: Openness of Cohen--Macaulay loci

The source characterizes Cohen--Macaulay points by flatness over a
quasi-finite polynomial cover, then applies openness of flatness.  The
localized fibre rings use the canonical quotient-localization model from
Chapter 112, while relative dimensions use Chapter 125's fibre prime.
-/

namespace Formalization.Books.Algebra.Unit130

open Set
open Formalization.Books.Algebra.Unit104
open Formalization.Books.Algebra.Unit112
open Formalization.Books.Algebra.Unit125
open Formalization.Books.Algebra.Unit129
open scoped TensorProduct

universe u

noncomputable section

/-! ## Source-facing Cohen--Macaulay loci -/

/- A local Cohen--Macaulay assertion packages the two typeclass hypotheses
   required by Chapter 104.  This is useful for localized fibre rings over an
   arbitrary base: their local and Noetherian instances are mathematical data
   of the fibre, rather than assumptions on the original base ring. -/
def IsCohenMacaulayLocalRingProperty
    (A : Type u) [CommRing A] : Prop :=
  ∃ hlocal : IsLocalRing A, ∃ hnoetherian : IsNoetherianRing A,
    letI : IsLocalRing A := hlocal
    letI : IsNoetherianRing A := hnoetherian
    IsCohenMacaulayLocalRing A

/- The Cohen--Macaulay condition at a point is the canonical local-ring
   condition applied to the localization at that prime. -/
def IsCohenMacaulayAt
    (S : Type u) [CommRing S] (q : PrimeSpectrum S) : Prop :=
  IsCohenMacaulayLocalRingProperty (Localization.AtPrime q.asIdeal)

/- The set of Cohen--Macaulay points of an affine spectrum. -/
def CohenMacaulayLocus
    (S : Type u) [CommRing S] : Set (PrimeSpectrum S) :=
  {q | IsCohenMacaulayAt S q}

/- The source writes the fibre at `q` as `S_q ⊗_R κ(p)`.  Chapter 112's
   `localRingOfFibre` is the canonical quotient-localization presentation of
   that local fibre ring.  The finite-type witness is retained because the
   source only uses this predicate in the finite-type setting. -/
def IsCohenMacaulayFibreAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (_hfinite : RingHom.FiniteType f)
    (q : PrimeSpectrum S) : Prop :=
  IsCohenMacaulayLocalRingProperty
    (localRingOfFibre f (PrimeSpectrum.comap f q) q rfl)

def CohenMacaulayFibreLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) :
    Set (PrimeSpectrum S) :=
  {q | IsCohenMacaulayFibreAt f hfinite q}

/- The locus in Lemma `lemma-finite-presentation-flat-CM-locus-open`, where
   both the fibre Cohen--Macaulay condition and the prescribed relative
   dimension hold. -/
def CohenMacaulayFibreDimensionLocus
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinite : RingHom.FiniteType f) (d : ℕ) :
    Set (PrimeSpectrum S) :=
  {q |
    IsCohenMacaulayFibreAt f hfinite q ∧
      relativeDimensionAt f hfinite (PrimeSpectrum.comap f q) q rfl = d}

/- Density in a fibre is density in the subtype carrying the fibre's induced
   topology.  This makes the phrase “dense in every fibre” source-faithful. -/
def DenseInFibre
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R)
    (U : Set (PrimeSpectrum S)) : Prop :=
  Dense
    ((fun q : {q : PrimeSpectrum S // PrimeSpectrum.comap f q = p} =>
        (q : PrimeSpectrum S)) ⁻¹' U)

/- A whole fibre is Cohen--Macaulay when its canonical tensor-product ring is
   Cohen--Macaulay in the global sense of Chapter 104. -/
def IsCohenMacaulayFibreRingAt
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (p : PrimeSpectrum R) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ hnoetherian : IsNoetherianRing
      (S ⊗[R] p.asIdeal.ResidueField),
    letI : IsNoetherianRing (S ⊗[R] p.asIdeal.ResidueField) := hnoetherian
    IsCohenMacaulayRing (S ⊗[R] p.asIdeal.ResidueField)

def AllFibresCohenMacaulay
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  ∀ p : PrimeSpectrum R, IsCohenMacaulayFibreRingAt f p

/- The package used for the final product decomposition: the three
   hypotheses (flat, finite presentation, and Cohen--Macaulay fibres) together
   with equidimensional fibres of the indicated dimension. -/
def IsFlatFinitePresentationWithCohenMacaulayEquidimensionalFibres
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (d : ℕ) : Prop :=
  RingHom.Flat f ∧
    RingHom.FinitePresentation f ∧
      AllFibresCohenMacaulayEquidimensional f d

/-! ## Flatness and the Cohen--Macaulay condition -/

/- The polynomial ring in the source is represented by `MvPolynomial (Fin d)
   k`.  Its map is an `AlgHom`, which records the compatibility with the
   given `k`-algebra structure on `S` needed by the relative-dimension claim. -/
theorem flatAtPrime_iff_isCohenMacaulayAt_and_relativeDimension
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (d : ℕ)
    (φ : MvPolynomial (Fin d) k →ₐ[k] S)
    (hquasi : RingHom.QuasiFinite φ.toRingHom) :
    let hfinite : RingHom.FiniteType (algebraMap k S) :=
      RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType k S)
    {q : PrimeSpectrum S |
        flatAtPrimeOverBaseRingHom (R := MvPolynomial (Fin d) k)
          (S := S) (M := S) φ.toRingHom q} =
      {q : PrimeSpectrum S |
        IsCohenMacaulayAt S q ∧
          relativeDimensionAt (algebraMap k S) hfinite
              (PrimeSpectrum.comap (algebraMap k S) q) q rfl = d} := by
  sorry

/- The set of Cohen--Macaulay local rings in a finite-type algebra over a
   field is open. -/
theorem isOpen_cohenMacaulayLocus_of_finiteType_over_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] :
    IsOpen (CohenMacaulayLocus S) := by
  sorry

/- The source's “generic CM” assertion is the conjunction that this locus is
   open and dense. -/
theorem cohenMacaulayLocus_is_dense_open
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] :
    IsOpen (CohenMacaulayLocus S) ∧ Dense (CohenMacaulayLocus S) := by
  sorry

/-! ## Flat finitely presented maps and their fibres -/

/- This is Lemma `lemma-finite-presentation-flat-CM-locus-open`. -/
theorem isOpen_cohenMacaulayFibreDimensionLocus_of_finitePresentation_flat
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    (hflat : RingHom.Flat f) (d : ℕ) :
    IsOpen
      (CohenMacaulayFibreDimensionLocus f
        (RingHom.FiniteType.of_finitePresentation hfinitePresentation) d) := by
  sorry

/- This is the source's statement that the Cohen--Macaulay fibre locus is
   open and fibrewise dense. -/
theorem cohenMacaulayFibreLocus_is_open_and_dense_in_fibres
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hfinitePresentation : RingHom.FinitePresentation f)
    (hflat : RingHom.Flat f) :
    let hfinite : RingHom.FiniteType f :=
      RingHom.FiniteType.of_finitePresentation hfinitePresentation
    IsOpen (CohenMacaulayFibreLocus f hfinite) ∧
      ∀ p : PrimeSpectrum R,
        DenseInFibre f p (CohenMacaulayFibreLocus f hfinite) := by
  sorry

/-! ## Field extensions and arbitrary base change -/

/- Cohen--Macaulayness is unchanged at corresponding points after extending
   the ground field.  The displayed square in the source proof is the square
   of these canonical localizations; its commutativity is already built into
   the `PrimeSpectrum.comap` hypothesis and no independent assertion is
   needed. -/
theorem isCohenMacaulayAt_iff_fieldExtension
    {k S K : Type u} [Field k] [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] [Field K] [Algebra k K]
    (q : PrimeSpectrum S)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (hlying :
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := k) (A := K) (B := S)).toRingHom
          qK = q) :
    IsCohenMacaulayAt S q ↔
      IsCohenMacaulayAt (K ⊗[k] S) qK := by
  sorry

/- Formation of the Cohen--Macaulay fibre locus commutes with arbitrary base
   change.  The map on spectra is the canonical map induced by the inclusion
   of `S` into `S ⊗[R] R'`. -/
theorem cohenMacaulayFibreLocus_baseChange
    {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    (f : R →+* S) (g : R →+* R')
    (hfinite : RingHom.FiniteType f) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R R' := g.toAlgebra
    let f' := Formalization.Books.Algebra.Unit14.baseChangeRingMap f g
    let hfinite' : RingHom.FiniteType f' :=
      Formalization.Books.Algebra.Unit14.baseChange_finite_type f g hfinite
    CohenMacaulayFibreLocus f' hfinite' =
      (PrimeSpectrum.comap
          (Formalization.Books.Algebra.Unit14.baseChangeAlgebraMap f g)) ⁻¹'
        CohenMacaulayFibreLocus f hfinite := by
  sorry

/-! ## Equidimensional decomposition -/

/- This is Lemma `lemma-relative-dimension-CM`.  The maps into the component
   rings and the compatibility equation with `f` make the product an explicit
   product of `R`-algebras, while `CommRingCat` reuses Mathlib's bundled ring
   structures for the components. -/
theorem exists_finite_product_of_flat_finitePresentation_CohenMacaulay_fibres
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : RingHom.Flat f)
    (hfinitePresentation : RingHom.FinitePresentation f)
    (hfibres : AllFibresCohenMacaulay f) :
    ∃ n : ℕ, ∃ components : Fin (n + 1) → CommRingCat.{u},
      ∃ componentMaps :
          ∀ i : Fin (n + 1), R →+* (components i : Type u),
        (∀ i : Fin (n + 1),
          IsFlatFinitePresentationWithCohenMacaulayEquidimensionalFibres
            (componentMaps i) i.1) ∧
          ∃ e : S ≃+* (∀ i : Fin (n + 1), (components i : Type u)),
            ∀ r : R, e (f r) = fun i => componentMaps i r := by
  sorry

end

end Formalization.Books.Algebra.Unit130
