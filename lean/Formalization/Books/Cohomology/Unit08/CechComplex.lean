import Formalization.Books.Cohomology.Unit08.MayerVietoris
import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Cohomology of Sheaves, Chapter 8: The Čech complex and Čech cohomology

This file uses Mathlib's canonical non-alternating Čech complex.  Its terms
are products indexed by finite strings of members of an open cover, and its
differential is the alternating sum of the face restriction maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04

universe v

namespace Formalization.Books.Cohomology.Unit08

/-! ## Covers and the Čech complex -/

/-- An open cover of an open subset, presented by a family of smaller opens. -/
structure CechOpenCover (X : TopCat.{v}) where
  /-- The open subset being covered. -/
  carrier : Opens X
  /-- The members of the cover. -/
  member : Type v
  /-- The open attached to each index. -/
  memberOpen : member → Opens X
  /-- Every member is contained in the open being covered. -/
  memberOpen_le_carrier : ∀ i, memberOpen i ≤ carrier
  /-- The members cover the carrier. -/
  cover : carrier = ⨆ i, memberOpen i

/-- The canonical Čech cochain complex of an abelian presheaf on a cover. -/
noncomputable def cechComplex {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) : CochainComplex AddCommGrpCat.{v} ℕ :=
  (CategoryTheory.cechComplexFunctor 𝒰.memberOpen).obj F

/-- The `p`th Čech cohomology object. -/
noncomputable def cechCohomologyObject {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (p : ℕ) : AddCommGrpCat.{v} :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) p).obj
    (cechComplex 𝒰 F)

/-- The `p`th Čech cochain object. -/
noncomputable abbrev cechCochainObject {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (p : ℕ) : AddCommGrpCat.{v} :=
  (cechComplex 𝒰 F).X p

/-- The Čech differential in degree `p`. -/
noncomputable abbrev cechDifferential {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (p : ℕ) :
    cechCochainObject 𝒰 F p ⟶ cechCochainObject 𝒰 F (p + 1) :=
  (cechComplex 𝒰 F).d p (p + 1)

/-- The displayed alternating Čech differential squares to zero. -/
theorem cechDifferential_squared {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (p : ℕ) :
    cechDifferential 𝒰 F p ≫ cechDifferential 𝒰 F (p + 1) = 0 := by
  exact (cechComplex 𝒰 F).d_comp_d p (p + 1) (p + 2)

/-! ## The augmentation and exactness assertions -/

/-- The canonical augmentation from sections on the covered open. -/
noncomputable def cechAugmentation {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) : F.obj (op 𝒰.carrier) ⟶ (cechComplex 𝒰 F).X 0 := by
  simpa [cechComplex, CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cosimplicialObjectFunctor,
    AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj,
    CategoryTheory.Limits.FormalCoproduct.cech,
    CategoryTheory.Limits.FormalCoproduct.power,
    CategoryTheory.Limits.FormalCoproduct.evalOp, Functor.comp_obj,
    Functor.comp, Functor.whiskeringLeft, Functor.rightOp] using
    (Pi.lift (fun i : Fin (0 + 1) → 𝒰.member =>
      let h : (∏ᶜ 𝒰.memberOpen ∘ i) ≤ 𝒰.carrier := le_trans
        (show (∏ᶜ 𝒰.memberOpen ∘ i) ≤ 𝒰.memberOpen (i 0) from
          leOfHom (Pi.π (fun a : Fin (0 + 1) => 𝒰.memberOpen (i a)) 0))
        (𝒰.memberOpen_le_carrier (i 0))
      F.map (homOfLE h).op))

/-- Exactness data for the augmented Čech complex. -/
structure AugmentedCechExactnessData {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) : Prop where
  augmentation_is_cycle :
    cechAugmentation 𝒰 F ≫ (cechComplex 𝒰 F).d 0 1 = 0
  augmentation_injective : Function.Injective (cechAugmentation 𝒰 F)
  exact_at_zero :
    (ShortComplex.mk (cechAugmentation 𝒰 F) ((cechComplex 𝒰 F).d 0 1)
      augmentation_is_cycle).Exact
  positive_exact : ∀ p : ℕ, 0 < p → (cechComplex 𝒰 F).ExactAt p

/-- Positive Čech cohomology vanishes exactly when the positive complex is exact. -/
def PositiveCechExactness {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (cechCohomologyObject 𝒰 F p)

/-- A contracting homotopy for the augmented Čech complex.  The first map
is the homotopy component in degree `-1`; the remaining components are the
usual maps `h : C^(p+1) → C^p`. -/
structure CechContractingHomotopyData {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (F : AbelianPresheaf X) where
  homotopy_minus_one : (cechComplex 𝒰 F).X 0 ⟶ F.obj (op 𝒰.carrier)
  homotopy : ∀ p : ℕ,
    (cechComplex 𝒰 F).X (p + 1) ⟶ (cechComplex 𝒰 F).X p
  on_degree_minus_one :
    cechAugmentation 𝒰 F ≫ homotopy_minus_one = 𝟙 _
  on_degree_zero :
    homotopy_minus_one ≫ cechAugmentation 𝒰 F +
        (cechComplex 𝒰 F).d 0 1 ≫ homotopy 0 = 𝟙 _
  on_positive_degrees : ∀ p : ℕ,
    homotopy p ≫ (cechComplex 𝒰 F).d p (p + 1) +
        (cechComplex 𝒰 F).d (p + 1) (p + 2) ≫ homotopy (p + 1) = 𝟙 _

/-- The sheaf condition is equivalent to exactness of the Čech augmentation
for every open cover. -/
theorem cech_h0_iff_isSheaf {X : TopCat.{v}} (F : AbelianPresheaf X) :
    TopCat.Presheaf.IsSheaf F ↔
      ∀ 𝒰 : CechOpenCover X, AugmentedCechExactnessData 𝒰 F := by
  sorry

/-- If one member of the cover is the covered open, the augmented Čech
complex is contractible.  The exactness data below is the source-facing
consequence of that homotopy equivalence. -/
theorem cech_trivial_cover {X : TopCat.{v}} (𝒰 : CechOpenCover X)
    (F : AbelianPresheaf X) (i : 𝒰.member) (hi : 𝒰.memberOpen i = 𝒰.carrier) :
    AugmentedCechExactnessData 𝒰 F := by
  sorry

/-- The explicit homotopy formulation of the trivial-cover lemma. -/
theorem cech_trivial_cover_contractible {X : TopCat.{v}}
    (𝒰 : CechOpenCover X) (F : AbelianPresheaf X)
    (i : 𝒰.member) (hi : 𝒰.memberOpen i = 𝒰.carrier) :
    Nonempty (CechContractingHomotopyData 𝒰 F) := by
  sorry

end Formalization.Books.Cohomology.Unit08
