import Formalization.Books.Algebra.Unit05.FiniteModules
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.FiniteType

/-!
# Commutative Algebra, Chapter 7: Finite ring maps

The source's definition of a finite ring map is Mathlib's canonical
`RingHom.Finite` predicate.  The module structure induced by a ring map on an
`S`-module is made explicit with `Module.compHom` in the statements below.
-/

namespace Formalization.Books.Algebra.Unit07

universe u v w

/-! ## Finite ring maps -/

/- The definition in the source is exactly `RingHom.Finite f`, whose body is
   `Module.Finite R S` for the algebra structure induced by `f`.  No parallel
   finite-map predicate is introduced here. -/

/-- A module over a finite ring extension is finite over the base ring exactly
when it is finite over the extension ring. -/
theorem finite_module_iff
    {R S M : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module S M]
    (f : R →+* S) (hf : RingHom.Finite f) :
    (letI : Module R M := Module.compHom M f; Module.Finite R M) ↔
      Module.Finite S M := by
  exact
    letI : Algebra R S := f.toAlgebra
    letI : Module R M := Module.compHom M f
    letI : Module.Finite R S := hf
    letI : IsScalarTower R S M := SMul.comp.isScalarTower f
    ⟨fun hM => Formalization.Books.Algebra.Unit05.finite_over_ringHom f hM,
      fun hM =>
        letI : Module.Finite S M := hM
        Module.Finite.trans S M⟩

/-- Finite ring maps are transitive under composition. -/
theorem finite_transitive
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hf : RingHom.Finite f) (hg : RingHom.Finite g) :
    RingHom.Finite (g.comp f) := by
  exact RingHom.Finite.comp hg hf

/-- A finite ring map is of finite type. -/
theorem finite_to_finiteType
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : RingHom.Finite f) :
    RingHom.FiniteType f := by
  exact RingHom.FiniteType.of_finite hf

/- The source's proof writes a finite module presentation using finitely many
   chosen module generators and finitely many relations, together with the
   displayed quotient presentation of the target algebra.  Mathlib packages
   exactly this construction in the canonical instance
   `Algebra.FinitePresentation.of_finitePresentation`, so the displayed
   quotient is accounted for without introducing a duplicate presentation
   structure. -/

/-- If the target is finitely presented as a module over the source, then the
ring map is finitely presented as an algebra. -/
theorem finitePresentation_of_moduleFinitePresentation
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hS : letI : Algebra R S := f.toAlgebra; Module.FinitePresentation R S) :
    RingHom.FinitePresentation f := by
  exact
    letI : Algebra R S := f.toAlgebra
    letI : Module.FinitePresentation R S := hS
    (inferInstance : Algebra.FinitePresentation R S)

end Formalization.Books.Algebra.Unit07
