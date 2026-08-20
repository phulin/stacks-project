import Formalization.Books.Modules.Unit16.TensorProduct
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Properties of Schemes, Chapter 17: Characterizing modules of finite type and finite presentation

The source section is `books/properties.tex:2075--2144`.  The affine lemmas
reuse the canonical `finiteType` and `IsFinitePresentation` predicates from
the Modules chapters and Mathlib's `AlgebraicGeometry.tilde` construction.
The introductory affine-local characterizations are expressed with an
explicit isomorphism from an affine open subscheme to a spectrum, so that the
associated module sheaf is transported along that isomorphism.
-/

namespace Formalization.Books.Properties.Unit17

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

/-! ## The affine-local characterizations in the introduction -/

/-- On an affine open, the source's phrase “of the form `M̃` for a finite
module” means that the restriction is isomorphic to the pullback of the
canonical tilde sheaf along a chosen affine-open identification. -/
def IsFiniteTypeTildeOnAffineOpen {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧
    ∃ (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
      (e : (U : Scheme) ≅ AlgebraicGeometry.Spec A),
      Module.Finite (A : Type u) (M : Type u) ∧
        Nonempty (F.restrict U.ι ≅
          (Scheme.Modules.pullback e.hom).obj (AlgebraicGeometry.tilde M))

/-- On an affine open, the source's phrase “of the form `M̃` for a finitely
presented module”, with the affine identification made explicit. -/
def IsFinitePresentationTildeOnAffineOpen {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) : Prop :=
  IsAffineOpen U ∧
    ∃ (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
      (e : (U : Scheme) ≅ AlgebraicGeometry.Spec A),
      Module.FinitePresentation (A : Type u) (M : Type u) ∧
        Nonempty (F.restrict U.ι ≅
          (Scheme.Modules.pullback e.hom).obj (AlgebraicGeometry.tilde M))

/-- The introductory affine-local formulation of finite type. -/
def IsFiniteTypeOnAffineOpens {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ U : X.Opens, IsFiniteTypeTildeOnAffineOpen F U

/-- The introductory affine-local formulation of finite presentation. -/
def IsFinitePresentationOnAffineOpens {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ U : X.Opens, IsFinitePresentationTildeOnAffineOpen F U

/-- For a quasi-coherent module, finite type is equivalent to being represented
on every affine open by the tilde of a finite module. -/
theorem finiteType_iff_on_affine_opens {X : Scheme.{u}} (F : X.Modules)
    (hF : Formalization.Books.Modules.Unit16.IsQuasiCoherent
      (O := AlgebraicGeometry.Scheme.sheaf X) F) :
    Formalization.Books.Modules.Unit16.IsFiniteType
      (O := AlgebraicGeometry.Scheme.sheaf X) F ↔
      IsFiniteTypeOnAffineOpens F := by
  sorry

/-- For a quasi-coherent module, finite presentation is equivalent to being
represented on every affine open by the tilde of a finitely presented module. -/
theorem finitePresentation_iff_on_affine_opens {X : Scheme.{u}} (F : X.Modules)
    (hF : Formalization.Books.Modules.Unit16.IsQuasiCoherent
      (O := AlgebraicGeometry.Scheme.sheaf X) F) :
    Formalization.Books.Modules.Unit16.IsFinitePresentation
      (O := AlgebraicGeometry.Scheme.sheaf X) F ↔
      IsFinitePresentationOnAffineOpens F := by
  sorry

/-! ## Lemma `lemma-finite-type-module` -/

/-- On an affine scheme, the tilde module is of finite type exactly when the
original module is finite. -/
theorem lemma_finite_type_module (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    Formalization.Books.Modules.Unit16.IsFiniteType
      (O := AlgebraicGeometry.Scheme.sheaf (AlgebraicGeometry.Spec R))
      (AlgebraicGeometry.tilde M) ↔
      Module.Finite (R : Type u) (M : Type u) := by
  sorry

/-! ## Lemma `lemma-finite-presentation-module` -/

/-- On an affine scheme, the tilde module is of finite presentation exactly
when the original module is finitely presented. -/
theorem lemma_finite_presentation_module
    (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    Formalization.Books.Modules.Unit16.IsFinitePresentation
      (O := AlgebraicGeometry.Scheme.sheaf (AlgebraicGeometry.Spec R))
      (AlgebraicGeometry.tilde M) ↔
      Module.FinitePresentation (R : Type u) (M : Type u) := by
  sorry

/-! The short exact sequence displayed in the proof of the finite-presentation
lemma is retained as a categorical interface.  The finite free source is
represented by the module on `Fin n`, and `tilde` is Mathlib's associated
module-sheaf functor. -/

/-- Tilde carries the kernel sequence of a surjection from a finite free
module to a short exact sequence of sheaves on the affine scheme. -/
theorem tilde_kernel_shortExact
    {R : CommRingCat.{u}} {M : ModuleCat.{u} R} (n : ℕ)
    (f : ModuleCat.of R (Fin n → R) ⟶ M) (hf : Epi f) :
    (ShortComplex.mk
      (AlgebraicGeometry.tilde.map (kernel.ι f))
      (AlgebraicGeometry.tilde.map f) (by sorry)).ShortExact := by
  sorry

end

end Formalization.Books.Properties.Unit17
