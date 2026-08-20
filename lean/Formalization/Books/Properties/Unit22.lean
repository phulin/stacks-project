import Mathlib.Algebra.Module.Projective
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Properties of Schemes, Chapter 22: Locally projective modules

The source section is `books/properties.tex:2714--2780`.  The affine-open
formulation uses Mathlib's canonical scheme-module sections and affine-open
subtype, while the module condition is the standard `Module.Projective`
predicate.
-/

namespace Formalization.Books.Properties.Unit22

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u v

noncomputable section

/-! ## Definition `definition-locally-projective` -/

/-- The local projectivity condition on a scheme module: its module of
sections over every affine open is projective over the corresponding ring of
functions.  The source applies this predicate to quasi-coherent modules. -/
def IsLocallyProjective {X : Scheme.{u}} (F : X.Modules) : Prop :=
  ∀ U : X.affineOpens,
    Module.Projective (Γ(X, U)) (Γ(F, U))

/-! ## Lemma `lemma-locally-projective` -/

/-- A quasi-coherent scheme module is locally projective exactly when this
condition is witnessed on one affine-open covering. -/
theorem lemma_locally_projective {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    IsLocallyProjective F ↔
      ∃ (I : Type v) (U : I → X.Opens),
        IsOpenCover U ∧
          ∀ i, IsAffineOpen (U i) ∧
            Module.Projective (Γ(X, U i)) (Γ(F, U i)) := by
  sorry

/-! The affine specialization in the same source lemma. -/

/-- On an affine scheme, the tilde module is locally projective exactly when
the original module is projective. -/
theorem lemma_locally_projective_affine (R : CommRingCat.{u})
    (M : ModuleCat.{u} R) :
    IsLocallyProjective (AlgebraicGeometry.tilde M) ↔
      Module.Projective (R : Type u) (M : Type u) := by
  sorry

/-! ## Lemma `lemma-locally-projective-pullback` -/

/-- Pullback preserves locally projective scheme modules. -/
theorem lemma_locally_projective_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Y.Modules) (hG : G.IsQuasicoherent)
    (hGproj : IsLocallyProjective G) :
    IsLocallyProjective ((Scheme.Modules.pullback f).obj G) := by
  sorry

end

end Formalization.Books.Properties.Unit22
