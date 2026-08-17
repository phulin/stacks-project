import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.PNat.Notation
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Formal Deformation Theory, Chapter 2: Notation and Conventions

The source's conventions are supplied by Mathlib's existing interfaces.  A
ring is represented by `[CommRing R]`, and the maximal ideal of a local ring
is `IsLocalRing.maximalIdeal R`.  Positive integers are the existing type
`ℕ+` (`PNat`).

For a category `C` and object `U`, the source's covariant representable
functor `Mor_C(U, -)` is `CategoryTheory.coyoneda.obj (Opposite.op U)`.
This is deliberately kept distinct from the contravariant Yoneda notation
used in other chapters; no chapter-local representable-functor definition is
needed.

For the coefficient data used throughout the chapter, Mathlib's canonical
interfaces are a Noetherian commutative ring `[CommRing Λ]
[IsNoetherianRing Λ]`, a field `[Field k]`, and a finite ring homomorphism
`f : Λ →+* k` with hypothesis `f.Finite`.  The kernel and image are already
`RingHom.ker f` and `RingHom.range f`.  The source's identification of the
image with the quotient by the kernel is represented by the existing first
isomorphism theorem `RingHom.quotientKerEquivRange f`, rather than by a
literal equality between two different types.
-/

namespace Formalization.Books.FormalDefos.Unit02

open CategoryTheory
open Opposite

universe u v

/-! ## Finite coefficient maps -/

/-- A finite map from a commutative ring to a field has maximal kernel. -/
theorem kernel_isMaximal_of_finite_to_field
    {Λ : Type u} [CommRing Λ]
    {k : Type v} [Field k] (f : Λ →+* k) (hf : f.Finite) :
    (RingHom.ker f).IsMaximal := by
  sorry

/-- The quotient by the kernel of a finite map to a field is a field. -/
theorem quotient_by_kernel_isField_of_finite_to_field
    {Λ : Type u} [CommRing Λ]
    {k : Type v} [Field k] (f : Λ →+* k) (hf : f.Finite) :
    IsField (Λ ⧸ RingHom.ker f) :=
  (Ideal.Quotient.maximal_ideal_iff_isField_quotient (RingHom.ker f)).mp
    (kernel_isMaximal_of_finite_to_field f hf)

/-- The image of a finite map from a commutative ring to a field is a field,
using the canonical bundled subring `RingHom.range f`. -/
theorem image_isField_of_finite_to_field
    {Λ : Type u} [CommRing Λ]
    {k : Type v} [Field k] (f : Λ →+* k) (hf : f.Finite) :
    IsField (RingHom.range f) := by
  sorry

/-- The target field is finite over the image field.  The inclusion is the
canonical subring homomorphism. -/
theorem target_finite_over_image_of_finite_to_field
    {Λ : Type u} [CommRing Λ]
    {k : Type v} [Field k] (f : Λ →+* k) (hf : f.Finite) :
    (RingHom.range f).subtype.Finite := by
  sorry

end Formalization.Books.FormalDefos.Unit02
