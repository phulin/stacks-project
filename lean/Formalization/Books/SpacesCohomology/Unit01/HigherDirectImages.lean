import Formalization.Books.SpacesCohomology.Unit01.Conventions

/-!
# Higher direct images

This file records the comparison, base-change, quasi-coherence, and affine
calculation statements in the source section.  Higher direct images and
cohomology are the operations supplied by the chapter's explicit site model.
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure SchemeRepresentation (X : AlgebraicSpace.{u}) where
  scheme : AlgebraicSpace.{u}
  equivalence : X ≅ scheme
  scheme_property : IsScheme scheme

theorem representable_cohomology_identification
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (F : SheafObj X) (hF : IsQuasiCoherent F)
    (r : SchemeRepresentation X) (i : ℤ) :
    CohomologyComparison X r.scheme F
      (pullbackSheaf r.equivalence.inv F) i i := by
  sorry

theorem representable_higher_direct_image_identification
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsRepresentable f)
    (hX : IsScheme X) (hY : IsScheme Y)
    (F : SheafObj X) (hF : IsQuasiCoherent F) (i : ℕ) :
    IsQuasiCoherent (higherDirectImage i f F) := by
  sorry

noncomputable def representableBaseChangeSpace {X Y V : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (v : SpaceHom V Y) : AlgebraicSpace.{u} :=
  baseChange f v

noncomputable def representableBaseChangeMap {X Y V : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (v : SpaceHom V Y) :
    SpaceHom (representableBaseChangeSpace f v) V :=
  baseChangeTarget f v

noncomputable def representableBaseChangeSheaf {X Y V : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (v : SpaceHom V Y) (F : SheafObj X) :
    SheafObj (representableBaseChangeSpace f v) :=
  pullbackSheaf (baseChangeSource f v) F

theorem representable_higher_direct_image_base_change
    (S X Y V : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (v : SpaceHom V Y)
    (hf : IsRepresentable f) (hqc : IsQuasiCompact f)
    (hqs : IsQuasiSeparated f) (hv : IsEtale v) (hv_surj : IsSurjective v)
    (F : SheafObj X) (hF : IsQuasiCoherent F) (i : ℕ) :
    Nonempty (SheafIso V
      (higherDirectImage i (representableBaseChangeMap f v)
        (representableBaseChangeSheaf f v F))
      (pullbackSheaf v (higherDirectImage i f F))) := by
  sorry

theorem higher_direct_image_is_quasi_coherent
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hqc : IsQuasiCompact f) (hqs : IsQuasiSeparated f)
    (F : SheafObj X) (hF : IsQuasiCoherent F) (i : ℕ) :
    IsQuasiCoherent (higherDirectImage i f F) := by
  sorry

theorem higher_direct_image_is_quasi_coherent_of_representable
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hf : IsRepresentable f)
    (hqc : IsQuasiCompact f) (hqs : IsQuasiSeparated f)
    (F : SheafObj X) (hF : IsQuasiCoherent F) (i : ℕ) :
    IsQuasiCoherent (higherDirectImage i f F) := by
  sorry

theorem quasi_coherence_higher_direct_images_application
    (S X Y V : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (v : SpaceHom V Y)
    (hqc : IsQuasiCompact f) (hqs : IsQuasiSeparated f)
    (hV : IsAffine (𝟙 V : SpaceHom V V))
    (F : SheafObj X) (hF : IsQuasiCoherent F) (q : ℕ) :
    CohomologyComparison (baseChange f v) V
      (representableBaseChangeSheaf f v F)
      (pullbackSheaf v (higherDirectImage q f F)) q 0 := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
