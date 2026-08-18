import Formalization.Books.SpacesCohomology.Unit03.HigherDirectImages

/-!
# Finite morphisms

The source warns that the étale statements below are not statements about
finite morphisms in the Zariski topology.  The declarations use the chapter
site model and retain the stalk, tensor, and derived projection-formula data.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure FiniteMorphismTopologyWarning where
  etale_site_scope : Prop
  zariski_counterexample_scope : Prop

structure ExactFinitePushforwardStatement
    {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) where
  preserves_short_exact : Prop
  higher_direct_image_zero : ∀ (p : ℕ), 0 < p →
    ∀ (F : SheafObj X), higherDirectImage p f F = zeroSheaf Y

theorem finite_higher_direct_image_zero
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsIntegral f) :
    Nonempty (ExactFinitePushforwardStatement f) := by
  sorry

theorem finite_pushforward_stalk
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsFinite f) (y : Y) (n : ℕ)
    (x : Fin n → X) (hx : ∀ i, f (x i) = y)
    (hx_injective : Function.Injective x)
    (hcomplete : ∀ z : X, f z = y ↔ ∃ i, z = x i)
    (F : SheafObj X) :
    Nonempty (Stalk Y (pushforwardSheaf f F) y ≃+
      (∀ i, Stalk X F (x i))) := by
  sorry

structure FiniteRingedToposSetup
    {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) where
  sourceRing : SheafObj X
  targetRing : SheafObj Y
  ringHom : SheafHom targetRing (pushforwardSheaf f sourceRing)
  ringHom_property : Prop

theorem finite_ringed_projection_formula
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsFinite f)
    (R : FiniteRingedToposSetup f)
    (F : SheafObj X) (G : SheafObj Y)
    (hF : Prop) (hG : Prop) :
    Nonempty (SheafIso Y
      (tensorSheaf Y G (pushforwardSheaf f F))
      (pushforwardSheaf f (tensorSheaf X (pullbackSheaf f G) F))) := by
  sorry

theorem finite_derived_projection_formula
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsFinite f)
    (R : FiniteRingedToposSetup f)
    (K : DerivedObj Y) (M : DerivedObj X) :
    Nonempty (DerivedIso Y
      (derivedTensor Y K (derivedDirectImage f M))
      (derivedDirectImage f (derivedTensor X (derivedPullback f K) M))) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
