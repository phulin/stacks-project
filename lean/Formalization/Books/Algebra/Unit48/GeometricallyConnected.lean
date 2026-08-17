import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Commutative Algebra, Chapter 48: Geometrically connected algebras

The source's geometric connectedness predicate is expressed using Mathlib's
`ConnectedSpace` on prime spectra.  The finite separable base-change test,
subalgebra and directed-colimit permanence statements, and the idempotent and
connected-component formulations of arbitrary base change are recorded with
the canonical algebra and topology APIs.
-/

namespace Formalization.Books.Algebra.Unit48

open scoped TensorProduct

universe u v w

noncomputable section

/-! ## Tensor products over a separably closed field -/

/-- Over a separably closed field, the tensor product of two algebras with
connected spectra has connected spectrum. -/
theorem separablyClosed_tensorProduct_connected
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [IsSepClosed k]
    (hR : ConnectedSpace (PrimeSpectrum R))
    (hS : ConnectedSpace (PrimeSpectrum S)) :
    ConnectedSpace (PrimeSpectrum (R ⊗[k] S)) := by
  sorry

/-! ## Geometric connectedness -/

/-- An algebra over a field is geometrically connected when every field base
change has connected spectrum. -/
def IsGeometricallyConnected (k : Type u) (S : Type v) [Field k]
    [CommRing S] [Algebra k S] : Prop :=
  ∀ (K : Type w) [Field K] [Algebra k K],
    ConnectedSpace (PrimeSpectrum (K ⊗[k] S))

/-- Geometric connectedness can be tested after finite separable extensions of
the base field. -/
theorem isGeometricallyConnected_iff_finiteSeparable
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S] :
    IsGeometricallyConnected k S ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [Algebra.IsSeparable k k'],
        ConnectedSpace (PrimeSpectrum (k' ⊗[k] S)) := by
  sorry

/- The equivalence above records the source's following remark that it is
   enough to check finite separable field extensions separately. -/

/-- Over a separably closed field, geometric connectedness is ordinary
connectedness of the spectrum. -/
theorem isGeometricallyConnected_iff_connectedSpectrum
    {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
    [IsSepClosed k] :
    IsGeometricallyConnected k R ↔ ConnectedSpace (PrimeSpectrum R) := by
  sorry

/-! ## Permanence properties -/

/-- Geometric connectedness descends to every `k`-subalgebra. -/
theorem isGeometricallyConnected_subalgebra
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : IsGeometricallyConnected k S) :
    ∀ A : Subalgebra k S, IsGeometricallyConnected k A := by
  sorry

/-- If all finitely generated `k`-subalgebras are geometrically connected,
then the ambient algebra is geometrically connected. -/
theorem isGeometricallyConnected_of_finiteType_subalgebras
    {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]
    (hS : ∀ A : Subalgebra k S, Algebra.FiniteType k A →
      IsGeometricallyConnected k A) :
    IsGeometricallyConnected k S := by
  sorry

/-- A directed colimit of geometrically connected `k`-algebras is
geometrically connected. -/
theorem isGeometricallyConnected_directLimit
    {k : Type u} [Field k] {ι : Type v} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] {A : ι → Type w} [∀ i, CommRing (A i)]
    [∀ i, Algebra k (A i)]
    (f : ∀ i j, i ≤ j → A i →ₐ[k] A j)
    [DirectedSystem A (f · · ·)]
    (hA : ∀ i, IsGeometricallyConnected k (A i)) :
    IsGeometricallyConnected k (DirectLimit A f) := by
  sorry

/-! ## Base change and connected components -/

/-- The map on idempotents induced by the canonical inclusion of the left
tensor factor. -/
def tensorLeftIdempotentMap
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] :
    {e : R // IsIdempotentElem e} →
      {e : R ⊗[k] S // IsIdempotentElem e} :=
  fun e =>
    ⟨Algebra.TensorProduct.includeLeftRingHom e,
      e.property.map Algebra.TensorProduct.includeLeftRingHom⟩

/-- Tensoring with a nonzero geometrically connected algebra preserves the
idempotents and connected components of the other algebra. -/
theorem geometricallyConnected_baseChange_idempotents_and_components
    {k R S : Type*} [Field k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Nontrivial S]
    (hS : IsGeometricallyConnected k S) :
    Function.Bijective
        (tensorLeftIdempotentMap (k := k) (R := R) (S := S)) ∧
      Function.Bijective
        ((PrimeSpectrum.continuous_comap
          (Algebra.TensorProduct.includeLeftRingHom :
            R →+* R ⊗[k] S)).connectedComponentsMap) := by
  sorry

end

end Formalization.Books.Algebra.Unit48
