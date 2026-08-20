import Formalization.Books.Schemes.Unit15.Representability

/-!
# Schemes, Chapter 16: Existence of fibre products of schemes

This file records the source section's finite-limit existence statement.  The underlying
construction and all categorical limit instances are Mathlib's canonical scheme APIs; the
locally-ringed-space cone below gives the source remark a chapter-owned interface.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Schemes.Unit16

universe u

/-! ## Existence of finite limits -/

/- The four interfaces below account for the source's equivalent formulations of the main
   lemma.  They are thin wrappers around the existing Mathlib instances. -/

theorem scheme_has_terminal : HasTerminal Scheme.{u} := by
  infer_instance

theorem scheme_has_binary_products : HasBinaryProducts Scheme.{u} := by
  infer_instance

theorem scheme_has_finite_products : HasFiniteProducts Scheme.{u} := by
  infer_instance

theorem scheme_has_pullbacks : HasPullbacks Scheme.{u} := by
  infer_instance

/-- The category of schemes has finite limits, hence in particular a terminal object, products,
and fibre products. -/
theorem scheme_has_finite_limits : HasFiniteLimits Scheme.{u} := by
  infer_instance

/-! ## The locally ringed space form of a scheme fibre product -/

/-- The scheme-theoretic fibre product, viewed as a pullback cone in locally ringed spaces. -/
def schemeFibreProductConeInLocallyRingedSpace
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    PullbackCone f.toLRSHom g.toLRSHom :=
  PullbackCone.mk
    (pullback.fst f g).toLRSHom
    (pullback.snd f g).toLRSHom
    (by
      simpa only [Scheme.Hom.comp_toLRSHom] using
        congrArg Scheme.Hom.toLRSHom (pullback.condition :
          pullback.fst f g ≫ f = pullback.snd f g ≫ g))

/-- The scheme fibre product cone is a pullback in the category of locally ringed spaces. -/
theorem schemeFibreProductConeInLocallyRingedSpace_isLimit
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Nonempty (IsLimit (schemeFibreProductConeInLocallyRingedSpace f g)) := by
  sorry

/-- The locally ringed space underlying the scheme fibre product is itself represented by a
scheme. -/
theorem schemeFibreProductConeInLocallyRingedSpace_is_scheme
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    Formalization.Books.Schemes.Unit09.IsSchemeLocallyRingedSpace
      (schemeFibreProductConeInLocallyRingedSpace f g).pt := by
  exact ⟨pullback f g, ⟨Iso.refl _⟩⟩

end Formalization.Books.Schemes.Unit16
