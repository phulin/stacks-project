import Formalization.Books.Modules.Unit16.TensorProduct
import Formalization.Books.Algebra.Unit13.TensorAlgebra
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.LinearAlgebra.TensorPower.Symmetric
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Sheaves of Modules, Chapter 21: Symmetric and exterior powers

The constructions in this chapter use the commutative sheaf-of-rings model
already used by Chapter 16. The sectionwise symmetric and exterior
presheaves are exposed through their sheaf-of-modules specifications.
-/

namespace Formalization.Books.Modules.Unit21

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Sheaves.Unit24
open Formalization.Books.Modules.Unit16
open scoped DirectSum TensorProduct

universe v

noncomputable section

/-! ## Tensor powers and the three graded algebras -/

/-- The degree-n tensor power of a sheaf of modules. -/
noncomputable def tensorPowerSheaf {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : ℕ → CommRingSheafModule O
  | 0 => SheafOfModules.unit (commRingSheafToRingSheaf O)
  | 1 => F
  | n + 2 => tensorProductSheaf O (tensorPowerSheaf O F (n + 1)) F

/-- The scalar action on a section module, transported from the underlying
commutative sheaf ring. -/
theorem sectionwiseModule_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (U : (Opens X)ᵒᵖ) :
    Nonempty (Module (↑(O.obj.obj U)) (↑(F.val.obj U))) := by
  sorry

noncomputable def sectionwiseModule {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (U : (Opens X)ᵒᵖ) :
    Module (↑(O.obj.obj U)) (↑(F.val.obj U)) :=
  Classical.choice (sectionwiseModule_exists O F U)

noncomputable def sectionwiseExteriorPowerModule {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ)
    (U : (Opens X)ᵒᵖ) : ModuleCat (↑(O.obj.obj U)) := by
  letI := sectionwiseModule O F U
  exact ModuleCat.of (↑(O.obj.obj U))
    (ExteriorAlgebra.exteriorPower (O.obj.obj U) n (↑(F.val.obj U)))

noncomputable def sectionwiseSymmetricPowerModule {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ)
    (U : (Opens X)ᵒᵖ) : ModuleCat (↑(O.obj.obj U)) := by
  letI := sectionwiseModule O F U
  exact ModuleCat.of (↑(O.obj.obj U))
    (SymmetricPower (O.obj.obj U) (ULift.{v} (Fin n)) (↑(F.val.obj U)))

/-- A graded sheaf algebra records the graded pieces and their multiplication.
The law propositions are explicit fields so later chapters can use the
grading interface without rebuilding it. -/
structure GradedSheafAlgebra {X : TopCat.{v}} (O : CommRingSheaf X) where
  component : ℕ → CommRingSheafModule O
  mul : ∀ n m, tensorProductSheaf O (component n) (component m) ⟶ component (n + m)
  one : SheafOfModules.unit (commRingSheafToRingSheaf O) ⟶ component 0
  gradedAlgebraLaws : Prop
  gradedAlgebraLaws_proof : gradedAlgebraLaws

/-- The tensor algebra data with its degree-zero and degree-one identifications. -/
structure TensorAlgebraData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) extends GradedSheafAlgebra O where
  component_eq : ∀ n, component n = tensorPowerSheaf O F n
  component_zero : Nonempty (component 0 ≅
    SheafOfModules.unit (commRingSheafToRingSheaf O))
  component_one : Nonempty (component 1 ≅ F)

theorem tensorAlgebraData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) :
    Nonempty (TensorAlgebraData O F) := by
  sorry

/-- The tensor algebra of a sheaf of modules. -/
noncomputable def tensorAlgebra {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : TensorAlgebraData O F :=
  Classical.choice (tensorAlgebraData_exists O F)

@[simp] theorem tensorAlgebra_component_eq {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    (tensorAlgebra O F).component n = tensorPowerSheaf O F n := by
  exact (tensorAlgebra O F).component_eq n

/-- The degree-n exterior power of a sheaf of modules is obtained by
sheafifying its sectionwise exterior-power presheaf. -/
structure SectionwiseExteriorPowerData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) where
  presheaf : PMod (commRingSheafToRingSheaf O).obj
  object_formula : ∀ U : (Opens X)ᵒᵖ, Nonempty
    (presheaf.obj U ≅ sectionwiseExteriorPowerModule O F n U)

theorem sectionwiseExteriorPowerData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    Nonempty (SectionwiseExteriorPowerData O F n) := by
  sorry

/-- The sectionwise exterior-power presheaf. -/
noncomputable def exteriorPowerPresheaf {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    PMod (commRingSheafToRingSheaf O).obj :=
  (Classical.choice (sectionwiseExteriorPowerData_exists O F n)).presheaf

theorem exteriorPowerPresheaf_obj_formula {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ)
    (U : (Opens X)ᵒᵖ) :
    Nonempty ((exteriorPowerPresheaf O F n).obj U ≅
      sectionwiseExteriorPowerModule O F n U) := by
  exact (Classical.choice (sectionwiseExteriorPowerData_exists O F n)).object_formula U

/-- The sheafified degree-n exterior power. -/
noncomputable def exteriorPowerSheaf {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (n : ℕ) : CommRingSheafModule O :=
  moduleSheafification (exteriorPowerPresheaf O F n)

/-- The degree-n symmetric power of a sheaf of modules is obtained by
sheafifying its sectionwise symmetric-power presheaf. -/
structure SectionwiseSymmetricPowerData {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) where
  presheaf : PMod (commRingSheafToRingSheaf O).obj
  object_formula : ∀ U : (Opens X)ᵒᵖ, Nonempty
    (presheaf.obj U ≅ sectionwiseSymmetricPowerModule O F n U)

theorem sectionwiseSymmetricPowerData_exists {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    Nonempty (SectionwiseSymmetricPowerData O F n) := by
  sorry

/-- The sectionwise symmetric-power presheaf. -/
noncomputable def symmetricPowerPresheaf {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    PMod (commRingSheafToRingSheaf O).obj :=
  (Classical.choice (sectionwiseSymmetricPowerData_exists O F n)).presheaf

theorem symmetricPowerPresheaf_obj_formula {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ)
    (U : (Opens X)ᵒᵖ) :
    Nonempty ((symmetricPowerPresheaf O F n).obj U ≅
      sectionwiseSymmetricPowerModule O F n U) := by
  exact (Classical.choice (sectionwiseSymmetricPowerData_exists O F n)).object_formula U

/-- The sheafified degree-n symmetric power. -/
noncomputable def symmetricPowerSheaf {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) (n : ℕ) : CommRingSheafModule O :=
  moduleSheafification (symmetricPowerPresheaf O F n)

/-- A graded algebra structure on the exterior powers. -/
structure ExteriorAlgebraData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) extends GradedSheafAlgebra O where
  component_eq : ∀ n, component n = exteriorPowerSheaf O F n
  gradedCommutativity : Prop
  gradedCommutativity_proof : gradedCommutativity

theorem exteriorAlgebraData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Nonempty (ExteriorAlgebraData O F) := by
  sorry

/-- The exterior algebra of a sheaf of modules. -/
noncomputable def exteriorAlgebra {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : ExteriorAlgebraData O F :=
  Classical.choice (exteriorAlgebraData_exists O F)

/-- A graded algebra structure on the symmetric powers. -/
structure SymmetricAlgebraData {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) extends GradedSheafAlgebra O where
  component_eq : ∀ n, component n = symmetricPowerSheaf O F n
  commutativity : Prop
  commutativity_proof : commutativity

theorem symmetricAlgebraData_exists {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : Nonempty (SymmetricAlgebraData O F) := by
  sorry

/-- The symmetric algebra of a sheaf of modules. -/
noncomputable def symmetricAlgebra {X : TopCat.{v}} (O : CommRingSheaf X)
    (F : CommRingSheafModule O) : SymmetricAlgebraData O F :=
  Classical.choice (symmetricAlgebraData_exists O F)

@[simp] theorem exteriorAlgebra_component_eq {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    (exteriorAlgebra O F).component n = exteriorPowerSheaf O F n := by
  exact (exteriorAlgebra O F).component_eq n

@[simp] theorem symmetricAlgebra_component_eq {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    (symmetricAlgebra O F).component n = symmetricPowerSheaf O F n := by
  exact (symmetricAlgebra O F).component_eq n

theorem symmetricAlgebra_is_commutative {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    (symmetricAlgebra O F).commutativity := by
  exact (symmetricAlgebra O F).commutativity_proof

theorem exteriorAlgebra_is_graded_commutative {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    (exteriorAlgebra O F).gradedCommutativity := by
  exact (exteriorAlgebra O F).gradedCommutativity_proof

/-! ## Local formulas -/

/-- The local exterior-power formula is the module sheafification of the
sectionwise exterior-power presheaf. -/
theorem local_exteriorPower_sheafification {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    Nonempty ((SheafOfModules.toSheaf (commRingSheafToRingSheaf O)).obj
        (exteriorPowerSheaf O F n) ≅
      (SheafOfModules.toSheaf (commRingSheafToRingSheaf O)).obj
        (moduleSheafification (exteriorPowerPresheaf O F n))) := by
  exact ⟨Iso.refl _⟩

/-- The local symmetric-power formula is the module sheafification of the
sectionwise symmetric-power presheaf. -/
theorem local_symmetricPower_sheafification {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) :
    Nonempty ((SheafOfModules.toSheaf (commRingSheafToRingSheaf O)).obj
        (symmetricPowerSheaf O F n) ≅
      (SheafOfModules.toSheaf (commRingSheafToRingSheaf O)).obj
        (moduleSheafification (symmetricPowerPresheaf O F n))) := by
  exact ⟨Iso.refl _⟩

/-! ## Stalks and pullback are exposed below. -/

/-! ## Stalks -/

/-- Stalks of the chosen sectionwise presheaves carry the induced scalar
action. -/
theorem stalkSectionModule_exists {X : TopCat.{v}}
    (O : CommRingSheaf X)
    (P : PMod (commRingSheafToRingSheaf O).obj) (x : X) :
    Nonempty (Module (↑(TopCat.Presheaf.stalk O.obj x))
      (↑(TopCat.Presheaf.stalk P.presheaf x))) := by
  sorry

noncomputable def stalkSectionModule {X : TopCat.{v}}
    (O : CommRingSheaf X)
    (P : PMod (commRingSheafToRingSheaf O).obj) (x : X) :
    Module (↑(TopCat.Presheaf.stalk O.obj x))
      (↑(TopCat.Presheaf.stalk P.presheaf x)) :=
  Classical.choice (stalkSectionModule_exists O P x)

/-- The sectionwise stalk object used in the stalk comparison. -/
noncomputable def exteriorPowerStalk {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O.obj x)) :=
  letI := stalkSectionModule O (exteriorPowerPresheaf O F n) x
  ModuleCat.of (↑(TopCat.Presheaf.stalk O.obj x))
    (↑(TopCat.Presheaf.stalk
      (exteriorPowerPresheaf O F n).presheaf x))

/-- The sectionwise stalk object used in the stalk comparison. -/
noncomputable def symmetricPowerStalk {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) (x : X) :
    ModuleCat (↑(TopCat.Presheaf.stalk O.obj x)) :=
  letI := stalkSectionModule O (symmetricPowerPresheaf O F n) x
  ModuleCat.of (↑(TopCat.Presheaf.stalk O.obj x))
    (↑(TopCat.Presheaf.stalk
      (symmetricPowerPresheaf O F n).presheaf x))

/-- The stalk comparison for the exterior power. -/
theorem stalk_exteriorPowerSheaf_iso {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) (x : X) :
    Nonempty (commRingSheafModuleStalk (exteriorPowerSheaf O F n) x ≅
      exteriorPowerStalk O F n x) := by
  sorry

/-- The stalk comparison for the symmetric power. -/
theorem stalk_symmetricPowerSheaf_iso {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) (x : X) :
    Nonempty (commRingSheafModuleStalk (symmetricPowerSheaf O F n) x ≅
      symmetricPowerStalk O F n x) := by
  sorry

/-- The stalk comparison for the tensor algebra, degree by degree. -/
theorem stalk_tensorAlgebra_iso {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) (n : ℕ) (x : X) :
    Nonempty
      (commRingSheafModuleStalk ((tensorAlgebra O F).component n) x ≅
        commRingSheafModuleStalk ((tensorAlgebra O F).component n) x) := by
  sorry

/-! ## Pullback -/

/-- Pullback preserves all three homogeneous power constructions. -/
theorem pullback_tensor_symmetric_exterior_iso
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (F : CommRingSheafModule OY) (n : ℕ) :
    Nonempty
      ((pullbackModule f α).obj ((tensorAlgebra OY F).component n) ≅
        (tensorAlgebra OX ((pullbackModule f α).obj F)).component n) ∧
    Nonempty
      ((pullbackModule f α).obj (symmetricPowerSheaf OY F n) ≅
        symmetricPowerSheaf OX ((pullbackModule f α).obj F) n) ∧
    Nonempty
      ((pullbackModule f α).obj (exteriorPowerSheaf OY F n) ≅
        exteriorPowerSheaf OX ((pullbackModule f α).obj F) n) := by
  sorry

/-! ## Presentations -/

/-- The two maps induced on symmetric powers by a presentation of F. -/
structure SymmetricPowerPresentationData
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) where
  left : tensorProductSheaf O F₂ (symmetricPowerSheaf O F₁ (n - 1)) ⟶
    symmetricPowerSheaf O F₁ n
  right : symmetricPowerSheaf O F₁ n ⟶ symmetricPowerSheaf O F n
  exact_right : RightExactSequence left right

theorem symmetricPowerPresentationData_exists
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) :
    Nonempty (SymmetricPowerPresentationData
      (X := X) (O := O) (F₂ := F₂) (F₁ := F₁) (F := F) n) := by
  sorry

noncomputable def symmetricPowerPresentationData
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) : SymmetricPowerPresentationData n :=
  Classical.choice (symmetricPowerPresentationData_exists
    (X := X) (O := O) (F₂ := F₂) (F₁ := F₁) (F := F) n hn h)

theorem symmetricPower_presentation_rightExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) :
    RightExactSequence
      (symmetricPowerPresentationData (X := X) (O := O)
        (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).left
      (symmetricPowerPresentationData (X := X) (O := O)
        (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).right := by
  exact (symmetricPowerPresentationData (X := X) (O := O)
    (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).exact_right

/-- The two maps induced on exterior powers by a presentation of F. -/
structure ExteriorPowerPresentationData
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) where
  left : tensorProductSheaf O F₂ (exteriorPowerSheaf O F₁ (n - 1)) ⟶
    exteriorPowerSheaf O F₁ n
  right : exteriorPowerSheaf O F₁ n ⟶ exteriorPowerSheaf O F n
  exact_right : RightExactSequence left right

theorem exteriorPowerPresentationData_exists
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) :
    Nonempty (ExteriorPowerPresentationData
      (X := X) (O := O) (F₂ := F₂) (F₁ := F₁) (F := F) n) := by
  sorry

noncomputable def exteriorPowerPresentationData
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) : ExteriorPowerPresentationData n :=
  Classical.choice (exteriorPowerPresentationData_exists
    (X := X) (O := O) (F₂ := F₂) (F₁ := F₁) (F := F) n hn h)

theorem exteriorPower_presentation_rightExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O} (n : ℕ) (hn : 0 < n)
    {f : F₂ ⟶ F₁} {g : F₁ ⟶ F}
    (h : RightExactSequence f g) :
    RightExactSequence
      (exteriorPowerPresentationData (X := X) (O := O)
        (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).left
      (exteriorPowerPresentationData (X := X) (O := O)
        (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).right := by
  exact (exteriorPowerPresentationData (X := X) (O := O)
    (F₂ := F₂) (F₁ := F₁) (F := F) n hn h).exact_right

/-! ## Permanence of homogeneous pieces and whole algebras -/

/-- All six permanence assertions from the source for the three degree-n
constructions. Coherence is stated for positive degree, as in the source. -/
theorem tensor_symmetric_exterior_permanence
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) (n : ℕ) (hn : 0 < n) :
    (IsLocallyGenerated F →
      IsLocallyGenerated (tensorPowerSheaf O F n) ∧
      IsLocallyGenerated (symmetricPowerSheaf O F n) ∧
      IsLocallyGenerated (exteriorPowerSheaf O F n)) ∧
    (IsFiniteType F →
      IsFiniteType (tensorPowerSheaf O F n) ∧
      IsFiniteType (symmetricPowerSheaf O F n) ∧
      IsFiniteType (exteriorPowerSheaf O F n)) ∧
    (IsFinitePresentation F →
      IsFinitePresentation (tensorPowerSheaf O F n) ∧
      IsFinitePresentation (symmetricPowerSheaf O F n) ∧
      IsFinitePresentation (exteriorPowerSheaf O F n)) ∧
    (IsCoherent F →
      IsCoherent (tensorPowerSheaf O F n) ∧
      IsCoherent (symmetricPowerSheaf O F n) ∧
      IsCoherent (exteriorPowerSheaf O F n)) ∧
    (IsQuasiCoherent F →
      IsQuasiCoherent (tensorPowerSheaf O F n) ∧
      IsQuasiCoherent (symmetricPowerSheaf O F n) ∧
      IsQuasiCoherent (exteriorPowerSheaf O F n)) ∧
    (IsLocallyFree F →
      IsLocallyFree (tensorPowerSheaf O F n) ∧
      IsLocallyFree (symmetricPowerSheaf O F n) ∧
      IsLocallyFree (exteriorPowerSheaf O F n)) := by
  sorry

/-- The whole algebra assertions are expressed componentwise, preserving the
graded direct-sum structure of the source. -/
def IsQuasiCoherentGradedAlgebra {X : TopCat.{v}} {O : CommRingSheaf X}
    (A : GradedSheafAlgebra O) : Prop :=
  ∀ n, IsQuasiCoherent (A.component n)

def IsLocallyFreeGradedAlgebra {X : TopCat.{v}} {O : CommRingSheaf X}
    (A : GradedSheafAlgebra O) : Prop :=
  ∀ n, IsLocallyFree (A.component n)

theorem whole_tensor_symmetric_exterior_permanence
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) :
    IsQuasiCoherent F →
      IsQuasiCoherentGradedAlgebra (tensorAlgebra O F) ∧
      IsQuasiCoherentGradedAlgebra (symmetricAlgebra O F) ∧
      IsQuasiCoherentGradedAlgebra ((exteriorAlgebra O F).toGradedSheafAlgebra) := by
  sorry

theorem whole_tensor_symmetric_exterior_locallyFree_permanence
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) :
    IsLocallyFree F →
      IsLocallyFreeGradedAlgebra (tensorAlgebra O F) ∧
      IsLocallyFreeGradedAlgebra (symmetricAlgebra O F) ∧
      IsLocallyFreeGradedAlgebra ((exteriorAlgebra O F).toGradedSheafAlgebra) := by
  sorry

/-! ## Infinite direct-sum warning -/

def InfiniteDirectSumsPreserveQuasiCoherent : Prop :=
  ∀ {X : TopCat.{v}} (O : CommRingSheaf X) (I : Type v)
    (_ : Infinite I) (G : I → CommRingSheafModule O),
    (∀ i, IsQuasiCoherent (G i)) →
      IsQuasiCoherent (directSum G)

def InfiniteDirectSumsPreserveLocallyFree : Prop :=
  ∀ {X : TopCat.{v}} (O : CommRingSheaf X) (I : Type v)
    (_ : Infinite I) (G : I → CommRingSheafModule O),
    (∀ i, IsLocallyFree (G i)) →
      IsLocallyFree (directSum G)

theorem not_infiniteDirectSumsPreserveQuasiCoherent :
    ¬ InfiniteDirectSumsPreserveQuasiCoherent := by
  sorry

theorem not_infiniteDirectSumsPreserveLocallyFree :
    ¬ InfiniteDirectSumsPreserveLocallyFree := by
  sorry

end
end Formalization.Books.Modules.Unit21
