import Formalization.Books.SpacesCohomology.Unit01.AlternatingCech
import Mathlib.Data.Set.Card

/-!
# Higher vanishing for quasi-coherent sheaves
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

theorem quasi_coherent_twist
    (S W U : AlgebraicSpace.{u}) (hS : IsScheme S)
    (Q : FiniteGroupQuotient W) (χ : SignCharacter Q.group)
    (T : TwistSheafData Q.quotient Q.group χ)
    (F : SheafObj Q.quotient) (hF : IsQuasiCoherent F) :
    IsQuasiCoherent (tensorSheaf Q.quotient F T.twist) := by
  sorry

structure AffineEtaleCoverData (X : AlgebraicSpace.{u}) where
  U : AlgebraicSpace.{u}
  map : SpaceHom U X
  scheme : IsScheme U
  affine : IsAffine (𝟙 U : SpaceHom U U)
  etale : IsEtale map
  surjective : IsSurjective map
  fibreBound : ℕ
  fibre_bound_property : ∀ x : X,
    IsFinitePointSet (FibrePoints map x) ∧
      Set.ncard (FibrePoints map x) ≤ fibreBound

def cohomologyVanishingAtLeast (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (d : ℕ) : Prop :=
  ∀ q : ℕ, d ≤ q → CohomologyVanishes X F q

theorem affine_etale_cover_vanishing
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (hqc : IsQuasiCompact (𝟙 X : SpaceHom X X))
    (hsep : IsSeparated (𝟙 X : SpaceHom X X))
    (C : AffineEtaleCoverData X)
    (F : SheafObj X) (hF : IsQuasiCoherent F) :
    cohomologyVanishingAtLeast X F C.fibreBound := by
  sorry

structure HigherVanishingChoices (X : AlgebraicSpace.{u}) where
  U : AlgebraicSpace.{u}
  f : SpaceHom U X
  U_scheme : IsScheme U
  U_affine : IsAffine (𝟙 U : SpaceHom U U)
  f_etale : IsEtale f
  f_surjective : IsSurjective f
  d : ℕ
  d_bounds_fibres : ∀ x : X,
    IsFinitePointSet (FibrePoints f x) ∧ Set.ncard (FibrePoints f x) ≤ d
  U_p : ℕ → AlgebraicSpace.{u}
  V_p : ℕ → AlgebraicSpace.{u}
  V_to_U : ∀ p, SpaceHom (V_p p) (U_p p)
  V_scheme : ∀ p, IsScheme (V_p p)
  V_affine : ∀ p, IsAffine (𝟙 (V_p p) : SpaceHom (V_p p) (V_p p))
  V_etale : ∀ p, IsEtale (V_to_U p)
  V_surjective : ∀ p, IsSurjective (V_to_U p)
  d_p : ℕ → ℕ
  d_p_bounds_fibres : ∀ p (x : U_p p),
    IsFinitePointSet (FibrePoints (V_to_U p) x) ∧
      Set.ncard (FibrePoints (V_to_U p) x) ≤ d_p p
  U_p_to_X : ∀ p, SpaceHom (U_p p) X
  U_p_etale : ∀ p, IsEtale (U_p_to_X p)
  bound : ℕ
  bound_spec : ∀ p, p ≤ d → p + d_p p ≤ bound

theorem higher_vanishing_choices_exist
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (hqc : IsQuasiCompact (𝟙 X : SpaceHom X X))
    (hqs : IsQuasiSeparated (𝟙 X : SpaceHom X X)) :
    Nonempty (HigherVanishingChoices X) := by
  sorry

theorem higher_vanishing_from_choices
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (C : HigherVanishingChoices X)
    (F : SheafObj X) (hF : IsQuasiCoherent F) :
    ∀ q : ℕ, C.bound ≤ q → CohomologyVanishes X F q := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
