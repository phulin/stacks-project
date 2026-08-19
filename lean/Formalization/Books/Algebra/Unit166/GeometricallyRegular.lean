import Formalization.Books.Algebra.Unit31.NoetherianRings
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Commutative Algebra, Chapter 166: Geometrically regular algebras

The source section uses the canonical Noetherian, regular, tensor-product,
smooth, faithfully-flat, finite-dimensional, algebraic, and separable APIs.
The source's introductory Noetherian observation is already represented by
`tensorProduct_isNoetherian_of_finiteType_fieldExtension` from Chapter 31.
-/

namespace Formalization.Books.Algebra.Unit166

open scoped TensorProduct

universe u v

noncomputable section

/-! ## The equivalence and definition -/

/-- For a Noetherian algebra over a field, regularity after every finitely
generated field extension is equivalent to regularity after every finite
purely inseparable field extension. -/
theorem isRegular_tensorProduct_iff_finitePurelyInseparable
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A] :
    (∀ (k' : Type u) [Field k'] [Algebra k k']
        [Algebra.FiniteType k k'],
        IsRegularRing (k' ⊗[k] A)) ↔
      ∀ (k' : Type u) [Field k'] [Algebra k k']
        [FiniteDimensional k k'] [IsPurelyInseparable k k'],
        IsRegularRing (k' ⊗[k] A) := by
  sorry

/-- A Noetherian algebra over a field is geometrically regular when all finite
purely inseparable field base changes are regular. -/
def IsGeometricallyRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A] : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsPurelyInseparable k k'],
    IsRegularRing (k' ⊗[k] A)

/-- A finitely generated field base change of a geometrically regular algebra
is geometrically regular over the larger field. -/
theorem isGeometricallyRegular_tensorProduct_of_finiteType
    {k K : Type u} {A : Type v} [Field k] [Field K] [CommRing A]
    [Algebra k K] [Algebra k A] [Algebra.FiniteType k K]
    [IsNoetherianRing A] (hA : IsGeometricallyRegular k A) :
    letI : IsNoetherianRing (K ⊗[k] A) :=
      Formalization.Books.Algebra.Unit31.tensorProduct_isNoetherian_of_finiteType_fieldExtension
        (k := k) (R := A) (K := K)
    letI : Algebra K (K ⊗[k] A) := Algebra.TensorProduct.leftAlgebra
    IsGeometricallyRegular K (K ⊗[k] A) := by
  sorry

/-! ## Descent and ascent -/

/-- Geometric regularity descends along faithfully flat maps of `k`-algebras. -/
theorem isGeometricallyRegular_of_faithfullyFlat
    {k : Type u} {A B : Type v} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →ₐ[k] B) (hff : RingHom.FaithfullyFlat f.toRingHom)
    (hB : IsGeometricallyRegular k B) :
    IsGeometricallyRegular k A := by
  sorry

/-- Geometric regularity ascends along smooth maps of `k`-algebras. -/
theorem isGeometricallyRegular_of_smooth
    {k : Type u} {A B : Type v} [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →ₐ[k] B) (hsmooth : RingHom.Smooth f.toRingHom)
    (hA : IsGeometricallyRegular k A) :
    IsGeometricallyRegular k B := by
  sorry

/-! ## Directed unions of subfields -/

/-- Geometric regularity passes from a directed union of subfields of the
base field.  The monotone covering family is the concrete subfield form of
the source's directed-colimit hypothesis. -/
theorem isGeometricallyRegular_of_directed_subfields
    {k : Type u} {A : Type v} [Field k] [CommRing A]
    [Algebra k A] [IsNoetherianRing A]
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (K : ι → Subfield k) (hK : Monotone K)
    (hcover : ∀ x : k, ∃ i : ι, x ∈ K i)
    (hA : ∀ i : ι,
      letI : Algebra (K i) A :=
        ((algebraMap k A).comp (K i).subtype).toAlgebra
      IsGeometricallyRegular (K i) A) :
    IsGeometricallyRegular k A := by
  sorry

/-! ## Separable algebraic base change -/

/-- For a separable algebraic field extension, geometric regularity is
independent of whether it is measured over the smaller or larger field. -/
theorem isGeometricallyRegular_iff_of_separableAlgebraic
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [Algebra.IsAlgebraic k k'] [Algebra.IsSeparable k k']
    {A : Type v} [CommRing A] [Algebra k' A] [IsNoetherianRing A] :
    letI : Algebra k A :=
      ((algebraMap k' A).comp (algebraMap k k')).toAlgebra
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k' A := by
  sorry

end
end Formalization.Books.Algebra.Unit166
