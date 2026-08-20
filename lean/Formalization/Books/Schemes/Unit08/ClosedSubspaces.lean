import Formalization.Books.Schemes.Unit04.ClosedImmersions
import Formalization.Books.Schemes.Unit07.AffineModules
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Schemes, Chapter 8: Closed subspaces of affine schemes

This file records the quotient-affine example and the classification statement from the
chapter.  The quotient morphism and the associated affine module sheaf use Mathlib's
canonical constructions; the locally-ringed-space closed-immersion interfaces are the
source-facing interfaces from Chapter 4.
-/

namespace Formalization.Books.Schemes.Unit08

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace
open Topology

universe u

noncomputable section

/-! ## The quotient affine closed immersion -/

abbrev affineSpec (R : Type u) [CommRing R] : Scheme.{u} :=
  AlgebraicGeometry.Spec (CommRingCat.of R)

abbrev affineSpecLocallyRingedSpace (R : Type u) [CommRing R] :
    Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u} :=
  Formalization.Books.Schemes.Unit05.affineLocallyRingedSpace R

abbrev quotientAffineSpec (R : Type u) [CommRing R] (I : Ideal R) : Scheme.{u} :=
  affineSpec (R ⧸ I)

abbrev quotientAffineSpecLocallyRingedSpace
    (R : Type u) [CommRing R] (I : Ideal R) :
    Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u} :=
  Formalization.Books.Schemes.Unit05.affineLocallyRingedSpace (R ⧸ I)

/-- The affine morphism `Spec (R / I) → Spec R` induced by the quotient map. -/
noncomputable def quotientAffineSpecMap (R : Type u) [CommRing R] (I : Ideal R) :
    quotientAffineSpec R I ⟶ affineSpec R :=
  AlgebraicGeometry.Spec.map
    (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The same quotient morphism viewed as a morphism of locally ringed spaces. -/
abbrev quotientAffineSpecLocallyRingedSpaceMap
    (R : Type u) [CommRing R] (I : Ideal R) :
    quotientAffineSpecLocallyRingedSpace R I ⟶ affineSpecLocallyRingedSpace R :=
  (quotientAffineSpecMap R I).toLRSHom

instance quotientAffineSpecMap_isClosedImmersion
    (R : Type u) [CommRing R] (I : Ideal R) :
    AlgebraicGeometry.IsClosedImmersion (quotientAffineSpecMap R I) := by
  exact AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    Ideal.Quotient.mk_surjective

/-- The quotient map is a homeomorphism onto a closed subset of the target. -/
theorem quotientAffineSpecMap_isClosedEmbedding
    (R : Type u) [CommRing R] (I : Ideal R) :
    IsClosedEmbedding (quotientAffineSpecMap R I).base := by
  exact AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
    (quotientAffineSpecMap R I)

/-- The quotient map is a closed immersion in the locally-ringed-space sense used earlier. -/
theorem quotientAffineSpecLocallyRingedSpaceMap_isClosedImmersion
    (R : Type u) [CommRing R] (I : Ideal R) :
    Formalization.Books.Schemes.Unit04.IsClosedImmersion
      (quotientAffineSpecLocallyRingedSpaceMap R I) := by
  sorry

/-! ## Points and the stalk quotient -/

/-- The point of `Spec (R / I)` lying over a prime `p` containing `I`. -/
noncomputable def quotientAffineSpecPoint
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) : PrimeSpectrum (R ⧸ I) :=
  { asIdeal := p.asIdeal.map (Ideal.Quotient.mk I)
    isPrime := p.asIdeal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (I.mk_ker.trans_le hp) }

theorem quotientAffineSpecPoint_base
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) :
    (quotientAffineSpecMap R I).base (quotientAffineSpecPoint I p hp) = p := by
  sorry

/-- The stalk quotient `R_p / I R_p` occurring at a point over `p`. -/
abbrev quotientAffineSpecStalkQuotient
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R) : Type u :=
  (Localization.AtPrime p.asIdeal) ⧸
    Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I

/-- The canonical quotient map `R_p → R_p / I R_p`. -/
noncomputable def quotientAffineSpecStalkQuotientMap
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal →+* quotientAffineSpecStalkQuotient I p :=
  Ideal.Quotient.mk _

/-!
The displayed stalk formula in the source is recorded as a commuting square of ring
equivalences.  This makes the two canonical identifications of affine stalks explicit while
retaining the source's map `R_p → R_p / I R_p`.
-/
theorem quotientAffineSpecLocallyRingedSpaceMap_stalkMap_is_quotient
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) :
    ∃ eX : Localization.AtPrime p.asIdeal ≃+*
        Formalization.Books.Schemes.Unit02.localRing
          (affineSpecLocallyRingedSpace R)
          ((quotientAffineSpecLocallyRingedSpaceMap R I).base
            (quotientAffineSpecPoint I p hp)),
      ∃ eZ : quotientAffineSpecStalkQuotient I p ≃+*
        Formalization.Books.Schemes.Unit02.localRing
          (quotientAffineSpecLocallyRingedSpace R I)
          (quotientAffineSpecPoint I p hp),
        eZ.toRingHom.comp (quotientAffineSpecStalkQuotientMap I p) =
          (Formalization.Books.Schemes.Unit02.stalkMap
            (quotientAffineSpecLocallyRingedSpaceMap R I)
            (quotientAffineSpecPoint I p hp)).hom.comp eX.toRingHom := by
  sorry

/-! ## The quasi-coherent ideal and its associated closed subspace -/

/-- The affine module sheaf `Ĩ` associated to an ideal `I ⊆ R`. -/
noncomputable def affineIdealSheafModule
    {R : Type u} [CommRing R] (I : Ideal R) :
    (Formalization.Books.Schemes.Unit07.affineScheme R).Modules :=
  AlgebraicGeometry.tilde (ModuleCat.of (CommRingCat.of R) I)

theorem affineIdealSheafModule_isQuasicoherent
    {R : Type u} [CommRing R] (I : Ideal R) :
    (affineIdealSheafModule I).IsQuasicoherent := by
  exact Formalization.Books.Schemes.Unit07.affineTilde_isQuasicoherent
    (ModuleCat.of (CommRingCat.of R) I)

/-- The ideal sheaf selected by the quotient closed immersion. -/
noncomputable def quotientAffineSpecIdealSheaf
    {R : Type u} [CommRing R] (I : Ideal R) :
    Formalization.Books.Schemes.Unit04.IdealSheaf
      (affineSpecLocallyRingedSpace R) :=
  Formalization.Books.Schemes.Unit04.closedImmersionIdeal
    (quotientAffineSpecLocallyRingedSpaceMap R I)

theorem quotientAffineSpecIdealSheaf_module_is_tilde
    {R : Type u} [CommRing R] (I : Ideal R) :
    Nonempty ((quotientAffineSpecIdealSheaf I).module ≅
      affineIdealSheafModule I) := by
  sorry

/-- The closed subspace associated to the quotient map's ideal sheaf. -/
noncomputable def quotientAffineSpecAssociatedClosedSubspace
    {R : Type u} [CommRing R] (I : Ideal R) :
    Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u} :=
  Formalization.Books.Schemes.Unit04.associatedClosedSubspaceOfClosedImmersion
    (quotientAffineSpecLocallyRingedSpaceMap R I)
    (quotientAffineSpecLocallyRingedSpaceMap_isClosedImmersion R I)

theorem quotientAffineSpec_is_associated_to_ideal_closedSubspace
    {R : Type u} [CommRing R] (I : Ideal R) :
    ∃ e : quotientAffineSpecLocallyRingedSpace R I ≅
        quotientAffineSpecAssociatedClosedSubspace I,
      e.hom ≫ Formalization.Books.Schemes.Unit04.closedSubspaceInclusion
        (affineSpecLocallyRingedSpace R) (quotientAffineSpecIdealSheaf I)
      (Formalization.Books.Schemes.Unit04.IsClosedImmersion.ideal_locallyGenerated
          (quotientAffineSpecLocallyRingedSpaceMap_isClosedImmersion R I)) =
        quotientAffineSpecLocallyRingedSpaceMap R I := by
  exact Formalization.Books.Schemes.Unit04.exists_closedImmersion_associatedIso
    (quotientAffineSpecLocallyRingedSpaceMap R I)
    (quotientAffineSpecLocallyRingedSpaceMap_isClosedImmersion R I)

/-! ## Classification of closed immersions into an affine -/

/-- A closed immersion into `Spec R` is identified with the quotient immersion for `I`. -/
def IsQuotientClosedImmersion
    {Z : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}}
    {R : Type u} [CommRing R]
    (i : Z ⟶ affineSpecLocallyRingedSpace R) (I : Ideal R) : Prop :=
  ∃ e : Z ≅ quotientAffineSpecLocallyRingedSpace R I,
    e.hom ≫ quotientAffineSpecLocallyRingedSpaceMap R I = i

/-- For an affine target, closed immersions are classified by unique ideals. -/
theorem exists_unique_ideal_of_closedImmersion
    {R : Type u} [CommRing R]
    {Z : Formalization.Books.Schemes.Unit02.LocallyRingedSpace.{u}}
    (i : Z ⟶ affineSpecLocallyRingedSpace R)
    (hi : Formalization.Books.Schemes.Unit04.IsClosedImmersion i) :
    ∃! I : Ideal R, IsQuotientClosedImmersion i I := by
  sorry

end

end Formalization.Books.Schemes.Unit08
