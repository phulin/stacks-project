import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Modules.Unit17.FlatModules
import Formalization.Books.Categories.Unit43.MonoidalCategories
import Mathlib.CategoryTheory.Retract
import Mathlib.Data.List.TFAE

/-!
# Sheaves of Modules, Chapter 18: Duals

The source section is `books/modules.tex:2805--2978`.  Chapter 16 supplies
the tensor product, associativity, and symmetry data.  The source also uses
the monoidal-category and internal-Hom interfaces; the former is made
explicit here because the current sheaf-of-modules API does not install a
global monoidal instance, and the latter is packaged by a representability
interface below rather than importing the future internal-Hom chapter.
-/

namespace Formalization.Books.Modules.Unit18

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Formalization.Books.Categories.Unit43
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit11
open Formalization.Books.Modules.Unit14
open Formalization.Books.Modules.Unit16
open Formalization.Books.Modules.Unit17
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22

universe v

noncomputable section

local notation "Mod" => Formalization.Books.Sheaves.Unit10.Mod

/-! ## The symmetric monoidal structure used by the source -/

abbrev sheafModuleUnit {X : TopCat.{v}} (O : CommRingSheaf X) :
    CommRingSheafModule O :=
  SheafOfModules.unit (commRingSheafToRingSheaf O)

theorem exists_sheafModuleLeftUnitor {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (∀ F : CommRingSheafModule O,
      tensorProductSheaf O (sheafModuleUnit O) F ≅ F) := by
  sorry

theorem exists_sheafModuleRightUnitor {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (∀ F : CommRingSheafModule O,
      tensorProductSheaf O F (sheafModuleUnit O) ≅ F) := by
  sorry

noncomputable def sheafModuleLeftUnitor {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    tensorProductSheaf O (sheafModuleUnit O) F ≅ F :=
  Classical.choice (exists_sheafModuleLeftUnitor O) F

noncomputable def sheafModuleRightUnitor {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    tensorProductSheaf O F (sheafModuleUnit O) ≅ F :=
  Classical.choice (exists_sheafModuleRightUnitor O) F

/- The data fields are the Chapter 16 tensor product and its canonical
   associator/unitors.  The coherence fields below are exactly the standard
   `MonoidalCategory` interface, so the dual declarations can reuse
   Mathlib's `ExactPairing` without creating a parallel notion of dual. -/
@[instance_reducible]
noncomputable def sheafModuleMonoidalCategory {X : TopCat.{v}}
    (O : CommRingSheaf X) : MonoidalCategory (CommRingSheafModule O) where
  tensorObj F G := tensorProductSheaf O F G
  whiskerLeft F _ _ g := tensorProductMap (𝟙 F) g
  whiskerRight := fun {X₁ X₂} f G => tensorProductMap f (𝟙 G)
  tensorHom := tensorProductMap
  tensorUnit := sheafModuleUnit O
  associator := fun F G H => tensorProductAssociativity F G H
  leftUnitor := sheafModuleLeftUnitor O
  rightUnitor := sheafModuleRightUnitor O
  tensorHom_def := by sorry
  id_tensorHom_id := by sorry
  tensorHom_comp_tensorHom := by sorry
  whiskerLeft_id := by sorry
  id_whiskerRight := by sorry
  associator_naturality := by sorry
  leftUnitor_naturality := by sorry
  rightUnitor_naturality := by sorry
  pentagon := by sorry
  triangle := by sorry

/-- The complete symmetric-monoidal package asserted at the start of the
chapter.  Its `symmetric` field uses Mathlib's canonical `SymmetricCategory`
interface; the Chapter 16 symmetry data supplies the underlying braiding. -/
structure SheafModuleSymmetricMonoidalData {X : TopCat.{v}}
    (O : CommRingSheaf X) where
  monoidal : MonoidalCategory (CommRingSheafModule O)
  monoidal_is_tensorProduct : monoidal = sheafModuleMonoidalCategory O
  symmetric : @CategoryTheory.SymmetricCategory (CommRingSheafModule O)
    (inferInstance : Category (CommRingSheafModule O)) monoidal

theorem exists_sheafModuleSymmetricMonoidalData {X : TopCat.{v}}
    (O : CommRingSheaf X) :
    Nonempty (SheafModuleSymmetricMonoidalData O) := by
  sorry

/- The symmetry family and its naturality are already the canonical
   `TensorProductSymmetryData` from Chapter 16. -/
theorem tensorProductSheaf_isSymmetric
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (TensorProductSymmetryData O) :=
  tensorProduct_symmetry_data_exists O

/-! ## Definition: locally a direct summand of a finite free module -/

/-- A sheaf of modules is locally a direct summand of a finite free module. -/
def IsLocallyDirectSummandOfFiniteFree {Y : RingedSpace.{v}}
    (F : Mod Y.structureSheaf) : Prop :=
  ∀ x : Y, ∃ U : Opens Y.carrier, x ∈ U ∧ ∃ n : ℕ,
    Nonempty (Retract
      (SheafOfModules.free (R := (ringedOpenSubspace Y U).structureSheaf)
        (ULift.{v} (Fin n)))
      ((openModuleRestrictionFunctor Y U).obj F))

abbrev IsLocallyDirectSummand {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  IsLocallyDirectSummandOfFiniteFree (Y := underlyingRingedSpace O) F

/-! ## Duals in the Chapter 16 tensor category -/

/-- The source's assertion that `F` has a left dual. -/
def HasLeftDual {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Prop :=
  letI := sheafModuleMonoidalCategory O
  ∃ G : CommRingSheafModule O,
    Nonempty (@ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F G)

/-! ## The three criteria in the introduction -/

theorem hasLeftDual_iff_isLocallyDirectSummand_iff_isFinitePresentation_and_isFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    List.TFAE [HasLeftDual O F, IsLocallyDirectSummand F,
      IsFinitePresentation F ∧ IsFlat O F] := by
  sorry

/-! ## The internal-Hom interface needed by Example 18.1 -/

/-- A sheaf representing maps out of `F` after tensoring on the left.

This is the chapter-local interface for the source's `SheafHom`; the future
internal-Hom chapter is deliberately not imported. -/
structure SheafModuleInternalHomData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) where
  hom : CommRingSheafModule O
  homEquiv : ∀ H : CommRingSheafModule O,
    (H ⟶ hom) ≃ (tensorProductSheaf O H F ⟶ G)
  homEquiv_natural : ∀ {H K : CommRingSheafModule O}
    (f : H ⟶ K) (g : K ⟶ hom),
    homEquiv H (f ≫ g) = tensorProductMap f (𝟙 F) ≫ homEquiv K g

theorem exists_sheafModuleInternalHomData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) :
    Nonempty (SheafModuleInternalHomData O F G) := by
  sorry

noncomputable def sheafModuleInternalHom {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) :
    CommRingSheafModule O :=
  (Classical.choice (exists_sheafModuleInternalHomData O F G)).hom

noncomputable def sheafModuleInternalHomEquiv {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G H : CommRingSheafModule O) :
    (H ⟶ sheafModuleInternalHom O F G) ≃
      (tensorProductSheaf O H F ⟶ G) :=
  (Classical.choice (exists_sheafModuleInternalHomData O F G)).homEquiv H

/-- Evaluation associated with the internal-Hom representability interface. -/
noncomputable def sheafModuleInternalHomEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) :
    tensorProductSheaf O (sheafModuleInternalHom O F G) F ⟶ G :=
  (sheafModuleInternalHomEquiv O F G
    (sheafModuleInternalHom O F G)) (𝟙 _)

/-- The source's map
`F ⊗ Hom(F, O) → Hom(F, F)`, defined by evaluation and currying. -/
noncomputable def finiteDualTensorToEndomorphism {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    tensorProductSheaf O F (sheafModuleInternalHom O F (sheafModuleUnit O)) ⟶
      sheafModuleInternalHom O F F := by
  letI : MonoidalCategory (CommRingSheafModule O) := sheafModuleMonoidalCategory O
  let dual := sheafModuleInternalHom O F (sheafModuleUnit O)
  let evaluation := sheafModuleInternalHomEvaluation O F (sheafModuleUnit O)
  let h : tensorProductSheaf O (tensorProductSheaf O F dual) F ⟶ F :=
    (tensorProductAssociativity F dual F).hom ≫
      (tensorProductMap (𝟙 F) evaluation) ≫ (sheafModuleRightUnitor O F).hom
  exact (sheafModuleInternalHomEquiv O F F
    (tensorProductSheaf O F dual)).symm h

/- The identity endomorphism is represented by the unit map under the
   internal-Hom equivalence.  This is the categorical form of the source's
   instruction that `eta` sends `1` to the tensor corresponding to
   `id_F`. -/
noncomputable def finiteDualIdentityMap {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    sheafModuleUnit O ⟶ sheafModuleInternalHom O F F :=
  (sheafModuleInternalHomEquiv O F F (sheafModuleUnit O)).symm
    (sheafModuleLeftUnitor O F).hom

/- Generic evaluation and coevaluation maps for an arbitrary left-dual
   pairing.  `ExactPairing` supplies the two snake identities, so no parallel
   dual structure or duplicate triangle fields are introduced here. -/
noncomputable def leftDualCoevaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O)
    (p : @ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F G) :
    sheafModuleUnit O ⟶ tensorProductSheaf O F G :=
  @ExactPairing.coevaluation (CommRingSheafModule O) _
    (sheafModuleMonoidalCategory O) F G p

noncomputable def leftDualEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O)
    (p : @ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F G) :
    tensorProductSheaf O G F ⟶ sheafModuleUnit O :=
  @ExactPairing.evaluation (CommRingSheafModule O) _
    (sheafModuleMonoidalCategory O) F G p

noncomputable def finiteDualCoevaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (p : @ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F
        (sheafModuleInternalHom O F (sheafModuleUnit O))) :
    sheafModuleUnit O ⟶
      tensorProductSheaf O F (sheafModuleInternalHom O F (sheafModuleUnit O)) :=
  leftDualCoevaluation O F (sheafModuleInternalHom O F (sheafModuleUnit O)) p

noncomputable def finiteDualCoevaluationFromIdentity {X : TopCat.{v}}
  (O : CommRingSheaf X) (F : CommRingSheafModule O)
    [IsIso (finiteDualTensorToEndomorphism O F)] :
    sheafModuleUnit O ⟶
      tensorProductSheaf O F (sheafModuleInternalHom O F (sheafModuleUnit O)) :=
  finiteDualIdentityMap O F ≫
    inv (finiteDualTensorToEndomorphism O F)

noncomputable def finiteDualEvaluation {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (p : @ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F
        (sheafModuleInternalHom O F (sheafModuleUnit O))) :
    tensorProductSheaf O (sheafModuleInternalHom O F (sheafModuleUnit O)) F ⟶
      sheafModuleUnit O :=
  leftDualEvaluation O F (sheafModuleInternalHom O F (sheafModuleUnit O)) p

/-! ## Example `example-dual` -/

/-- The tensor-to-endomorphism map is an isomorphism for a locally finite
projective sheaf. -/
theorem finiteDualTensorToEndomorphism_isIso_of_isLocallyDirectSummand
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsLocallyDirectSummand F) :
    IsIso (finiteDualTensorToEndomorphism O F) := by
  sorry

/-- The canonical tensor-to-endomorphism map for a locally finite projective
sheaf, together with its isomorphism property. -/
structure FiniteDualEndomorphismData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) where
  isIsoTensorToEndomorphism : IsIso (finiteDualTensorToEndomorphism O F)

theorem exists_finiteDualEndomorphismData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsLocallyDirectSummand F) :
    Nonempty (FiniteDualEndomorphismData O F) := by
  sorry

/-- The evaluation map of the finite dual. -/
structure FiniteDualData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) where
  tensorToEndomorphism_isIso : IsIso (finiteDualTensorToEndomorphism O F)
  pairing : @ExactPairing (CommRingSheafModule O) _
    (sheafModuleMonoidalCategory O) F
      (sheafModuleInternalHom O F (sheafModuleUnit O))
  coevaluation_identity :
    finiteDualCoevaluation O F pairing = finiteDualCoevaluationFromIdentity O F
  evaluation_is_internalHom_evaluation :
    finiteDualEvaluation O F pairing =
      sheafModuleInternalHomEvaluation O F (sheafModuleUnit O)

theorem exists_finiteDualData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsLocallyDirectSummand F) :
    Nonempty (FiniteDualData O F) := by
  sorry

theorem hasLeftDual_of_isLocallyDirectSummand
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsLocallyDirectSummand F) :
    HasLeftDual O F := by
  sorry

/-! ## Lemma `lemma-left-dual-module` -/

theorem locallyDirectSummandOfFiniteFree_of_hasLeftDual
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : HasLeftDual O F) :
    IsLocallyDirectSummand F := by
  sorry

/-! The source's canonical comparison `e : Hom(F, O) ≅ G` and its
   sectionwise evaluation formula are recorded as one usable interface. -/
structure LeftDualComparisonData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) where
  comparisonIso : sheafModuleInternalHom O F (sheafModuleUnit O) ≅ G
  pairing : @ExactPairing (CommRingSheafModule O) _
    (sheafModuleMonoidalCategory O) F G
  comparison_inverse_formula :
    comparisonIso.inv =
      (sheafModuleInternalHomEquiv O F (sheafModuleUnit O) G).symm
        (leftDualEvaluation O F G pairing)

theorem leftDual_comparison
    {X : TopCat.{v}} (O : CommRingSheaf X)
    (F G : CommRingSheafModule O)
    (hFG : Nonempty (@ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F G)) :
    Nonempty (LeftDualComparisonData O F G) := by
  sorry

/-! ## Lemma `lemma-flat-locally-finite-presentation` -/

/-- The finite-presentation and flatness criterion for local finite projectivity. -/
theorem locallyDirectSummandOfFiniteFree_of_isFinitePresentation_of_isFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsFinitePresentation F) (hflat : IsFlat O F) :
    IsLocallyDirectSummand F := by
  sorry

/-! ## Explicit proof interfaces from the two source proofs -/

/-- The finite-free factorization extracted from the local dual coordinates. -/
structure LocalFiniteFreeFactorization {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) where
  U : Opens X
  n : ℕ
  inclusion :
    (openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj F ⟶
      SheafOfModules.free
        (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin n))
  retraction :
    SheafOfModules.free
        (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin n)) ⟶
      (openModuleRestrictionFunctor (underlyingRingedSpace O) U).obj F
  retract_eq : inclusion ≫ retraction = 𝟙 _

/-- The iterated local factorization data in the flat finite-presentation proof. -/
structure FlatFinitePresentationFactorization {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) where
  U : Opens X
  r : ℕ
  n : ℕ
  relationMap :
    SheafOfModules.free
        (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin r)) ⟶
      SheafOfModules.free
        (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin n))
  presentationMap :
    SheafOfModules.free
        (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
        (ULift.{v} (Fin n)) ⟶ restrictedModule O F U
  presentation_section :
    restrictedModule O F U ⟶ SheafOfModules.free
      (R := (ringedOpenSubspace (underlyingRingedSpace O) U).structureSheaf)
      (ULift.{v} (Fin n))
  relation_comp_presentation : relationMap ≫ presentationMap = 0
  presentation_split : presentationMap ≫ presentation_section = 𝟙 _
  presentation_epi : Epi presentationMap
  presentation_exact :
    (ShortComplex.mk relationMap presentationMap
      relation_comp_presentation).Exact

theorem exists_localFiniteFreeFactorization_of_hasLeftDual
    {X : TopCat.{v}} (O : CommRingSheaf X) (F G : CommRingSheafModule O)
    (hFG : Nonempty (@ExactPairing (CommRingSheafModule O) _
      (sheafModuleMonoidalCategory O) F G)) (x : X) :
    ∃ d : LocalFiniteFreeFactorization O F, x ∈ d.U := by
  sorry

theorem exists_flatFinitePresentationFactorization_of_isFinitePresentation_of_isFlat
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O)
    (hF : IsFinitePresentation F) (hflat : IsFlat O F) :
    ∀ x : X, ∃ d : FlatFinitePresentationFactorization O F, x ∈ d.U := by
  sorry

end

end Formalization.Books.Modules.Unit18
