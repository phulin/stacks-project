import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-!
# Commutative Algebra, Chapter 6: Ring maps of finite type and of finite presentation

The source's two finiteness notions are represented by Mathlib's canonical
`RingHom.FiniteType` and `RingHom.FinitePresentation` predicates.  Polynomial
rings in the source are represented by `MvPolynomial (Fin n) R`, and finitely
generated ideals by `Ideal.FG`.
-/

namespace Formalization.Books.Algebra.Unit06

universe u v w

/-! ## Finite type and finite presentation -/

/- The definition of finite type is `RingHom.FiniteType f`: the target is a
   finitely generated algebra over the source.  The definition of finite
   presentation is `RingHom.FinitePresentation f`: the target is a finitely
   presented algebra over the source.  These are the source definitions, so
   no parallel predicates are introduced here. -/

/-! ## Composition and change of base -/

/-- Finite type ring maps are stable under composition. -/
theorem finiteType_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.FiniteType f) (hg : RingHom.FiniteType g) :
    RingHom.FiniteType (g.comp f) := by
  sorry

/- The source's finite-presentation composition assertion. -/
/-- Finitely presented ring maps are stable under composition. -/
theorem finitePresentation_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.FinitePresentation f)
    (hg : RingHom.FinitePresentation g) :
    RingHom.FinitePresentation (g.comp f) := by
  sorry

/- The source's third assertion says that a factor of a finite-type composite
   is finite type.  This is the standard `of_comp_finiteType` interface. -/
/-- If a composite is of finite type, then its second map is of finite type. -/
theorem finiteType_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (h : RingHom.FiniteType (g.comp f)) :
    RingHom.FiniteType g := by
  sorry

/- The source's fourth assertion is the finite-presentation version of the
   preceding factor statement. -/
/-- If the composite is finitely presented and the first map is of finite type,
then the second map is finitely presented. -/
theorem finitePresentation_of_comp
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hcomp : RingHom.FinitePresentation (g.comp f))
    (hf : RingHom.FiniteType f) :
    RingHom.FinitePresentation g := by
  sorry

/-! ## Independence of a finite presentation -/

/- In the source, `R[x₁, ..., xₙ]` is the finite-variable polynomial ring
   `MvPolynomial (Fin n) R`. -/
/-- A surjection from a finite-variable polynomial ring onto a finitely
presented algebra has finitely generated kernel. -/
theorem finitePresentation_kernel_fg_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hS : RingHom.FinitePresentation f) (n : ℕ)
    (α : letI : Algebra R S := f.toAlgebra
      MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α) :
    letI : Algebra R S := f.toAlgebra
    (RingHom.ker α.toRingHom).FG := by
  sorry

/-! ## Finitely presented modules over a finite-type subring -/

/- The R-module structure in the source is the one induced by the ring map.
   The `letI` binders make that choice explicit and prevent an unrelated
   pre-existing R-module structure from being used. -/
/-- An S-module finitely presented over R remains finitely presented over S when
the map R → S is of finite type. -/
theorem finitePresentation_module_over_finiteType
    {R S M : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) [AddCommGroup M] [Module S M]
    (hS : RingHom.FiniteType f)
    (hM : letI : Module R M := Module.compHom M f
      Module.FinitePresentation R M) :
    letI : Module R M := Module.compHom M f
    Module.FinitePresentation S M := by
  sorry

end Formalization.Books.Algebra.Unit06
