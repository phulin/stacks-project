import Formalization.Books.Modules.Unit12.Coherent
import Formalization.Books.Modules.Unit14.LocallyFree
import Formalization.Books.Modules.Unit15.BilinearMaps
import Formalization.Books.Sheaves.Unit24.Modules
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Sheaves of Modules, Chapter 16: Tensor product

The source uses tensor products of modules over a ringed space.  The
sectionwise tensor product is canonically symmetric when the structure sheaf
is commutative, so this file uses Mathlib's `CommRingSheaf` model and keeps
the underlying sheaf-of-modules constructions visible.
-/

namespace Formalization.Books.Modules.Unit16

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MonoidalCategory
open Formalization.Books.Modules.Unit03
open Formalization.Books.Modules.Unit08
open Formalization.Books.Modules.Unit09
open Formalization.Books.Modules.Unit10
open Formalization.Books.Modules.Unit11
open Formalization.Books.Modules.Unit12
open Formalization.Books.Modules.Unit14
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit06
open Formalization.Books.Sheaves.Unit17
open Formalization.Books.Sheaves.Unit22
open Formalization.Books.Sheaves.Unit24

universe u v

noncomputable section

/-! ## Tensor product presheaves and sheaves -/

/-- The presheaf tensor product, computed sectionwise by Mathlib's canonical
tensor product of presheaves of modules. -/
noncomputable def tensorProductPresheaf {X : TopCat.{v}}
    {O : CommRingSheaf X} (F G : CommRingSheafModule O) :
    PMod (commRingSheafToRingSheaf O).obj :=
  PresheafOfModules.Monoidal.tensorObj F.val G.val

/-- Sheafification of a presheaf of modules over a commutative sheaf of rings. -/
noncomputable abbrev moduleSheafification {X : TopCat.{v}}
    {O : CommRingSheaf X}
    (P : PMod (commRingSheafToRingSheaf O).obj) :
    CommRingSheafModule O :=
  (PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf O).obj)).obj P

/-- The tensor product sheaf is the sheafification of the sectionwise tensor
product presheaf.  This is the chapter-owned name for the construction; its
body is the standard Mathlib sheafification. -/
noncomputable abbrev tensorProductSheaf {X : TopCat.{v}}
    (O : CommRingSheaf X) (F G : CommRingSheafModule O) :
    CommRingSheafModule O :=
  moduleSheafification (tensorProductPresheaf F G)

/-- A morphism induced by maps in both tensor factors. -/
noncomputable def tensorProductMap {X : TopCat.{v}}
    {O : CommRingSheaf X}
    {F₁ F₂ G₁ G₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    tensorProductSheaf O F₁ G₁ ⟶ tensorProductSheaf O F₂ G₂ :=
  (PresheafOfModules.sheafification
    (𝟙 (commRingSheafToRingSheaf O).obj)).map
    (PresheafOfModules.Monoidal.tensorHom f.val g.val)

/-- The tensor product is functorial in each factor. -/
theorem tensorProductMap_id {X : TopCat.{v}} {O : CommRingSheaf X}
    {F G : CommRingSheafModule O} :
    tensorProductMap (𝟙 F) (𝟙 G) = 𝟙 (tensorProductSheaf O F G) := by
  sorry

theorem tensorProductMap_comp {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ F₃ G₁ G₂ G₃ : CommRingSheafModule O}
    (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    (g₁ : G₁ ⟶ G₂) (g₂ : G₂ ⟶ G₃) :
    tensorProductMap (f₁ ≫ f₂) (g₁ ≫ g₂) =
      tensorProductMap f₁ g₁ ≫ tensorProductMap f₂ g₂ := by
  sorry

/-! ## The universal property, symmetry, and associativity -/

/-- The chapter's bilinear maps, specialized to a commutative sheaf of rings.
This reuses the Chapter 15 sectionwise bilinear-map interface. -/
abbrev BilinearMaps {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G H : CommRingSheafModule O) :=
  Formalization.Books.Modules.Unit15.SheafBilinearMap F G H

/-- The universal property of the tensor product sheaf. -/
theorem tensorProduct_hom_equiv_bilinearMaps
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G H : CommRingSheafModule O) :
    Nonempty ((tensorProductSheaf O F G ⟶ H) ≃ BilinearMaps F G H) := by
  sorry

/-- A symmetry family, including the functoriality asserted in the source. -/
structure TensorProductSymmetryData {X : TopCat.{v}}
    (O : CommRingSheaf X) where
  symmetry : ∀ F G : CommRingSheafModule O,
    tensorProductSheaf O F G ≅ tensorProductSheaf O G F
  naturality : ∀ {F₁ F₂ G₁ G₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂),
    (symmetry F₁ G₁).hom ≫ tensorProductMap g f =
      tensorProductMap f g ≫ (symmetry F₂ G₂).hom

/-- Existence of the canonical symmetry family. -/
theorem tensorProduct_symmetry_data_exists
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (TensorProductSymmetryData O) := by
  sorry

/-- The canonical symmetry family. -/
noncomputable def tensorProductSymmetryData
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    TensorProductSymmetryData O :=
  Classical.choice (tensorProduct_symmetry_data_exists O)

/-- The canonical symmetry isomorphism. -/
noncomputable abbrev tensorProductSymmetry
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) :
    tensorProductSheaf O F G ≅ tensorProductSheaf O G F :=
  (tensorProductSymmetryData O).symmetry F G

theorem tensorProduct_symmetry_natural
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ G₁ G₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    (tensorProductSymmetry F₁ G₁).hom ≫ tensorProductMap g f =
      tensorProductMap f g ≫ (tensorProductSymmetry F₂ G₂).hom := by
  exact (tensorProductSymmetryData O).naturality f g

/-- An associativity family, including the functoriality asserted in the
source. -/
structure TensorProductAssociativityData {X : TopCat.{v}}
    (O : CommRingSheaf X) where
  associativity : ∀ F G H : CommRingSheafModule O,
    tensorProductSheaf O (tensorProductSheaf O F G) H ≅
      tensorProductSheaf O F (tensorProductSheaf O G H)
  naturality : ∀ {F₁ F₂ G₁ G₂ H₁ H₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (h : H₁ ⟶ H₂),
    tensorProductMap (tensorProductMap f g) h ≫
          (associativity F₂ G₂ H₂).hom =
      (associativity F₁ G₁ H₁).hom ≫
        tensorProductMap f (tensorProductMap g h)

/-- Existence of the canonical associativity family. -/
theorem tensorProduct_associativity_data_exists
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    Nonempty (TensorProductAssociativityData O) := by
  sorry

/-- The canonical associativity family. -/
noncomputable def tensorProductAssociativityData
    {X : TopCat.{v}} (O : CommRingSheaf X) :
    TensorProductAssociativityData O :=
  Classical.choice (tensorProduct_associativity_data_exists O)

/-- The canonical associativity isomorphism. -/
noncomputable abbrev tensorProductAssociativity
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G H : CommRingSheafModule O) :
    tensorProductSheaf O (tensorProductSheaf O F G) H ≅
      tensorProductSheaf O F (tensorProductSheaf O G H) :=
  (tensorProductAssociativityData O).associativity F G H

theorem tensorProduct_associativity_natural
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ G₁ G₂ H₁ H₂ : CommRingSheafModule O}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) (h : H₁ ⟶ H₂) :
    tensorProductMap (tensorProductMap f g) h ≫
          (tensorProductAssociativity F₂ G₂ H₂).hom =
      (tensorProductAssociativity F₁ G₁ H₁).hom ≫
        tensorProductMap f (tensorProductMap g h) := by
  exact (tensorProductAssociativityData O).naturality f g h

/-! ## Stalks and sheafification -/

/-- The stalk-level tensor product appearing in the stalk comparison. -/
noncomputable abbrev stalkTensorProduct {X : TopCat.{v}}
    {O : CommRingSheaf X} (F G : CommRingSheafModule O) (x : X) :=
  (commRingSheafModuleStalk F x) ⊗ (commRingSheafModuleStalk G x)

/-- Tensor products commute with taking stalks. -/
theorem stalk_tensorProductSheaf_iso
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) (x : X) :
    Nonempty
      (commRingSheafModuleStalk (tensorProductSheaf O F G) x ≅
        stalkTensorProduct F G x) := by
  sorry

/-- Sheafification commutes with the tensor-product construction. -/
theorem tensorProduct_sheafification
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F' G' : PMod (commRingSheafToRingSheaf O).obj) :
    Nonempty
      (tensorProductSheaf O (moduleSheafification F') (moduleSheafification G') ≅
        moduleSheafification (PresheafOfModules.Monoidal.tensorObj F' G')) := by
  sorry

/-! ## Right exactness -/

/-- A convenient source-facing package for a right exact sequence. -/
structure RightExactSequence {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {F₁ F₂ F₃ : C}
    (f : F₁ ⟶ F₂) (g : F₂ ⟶ F₃) : Prop where
  map_comp : f ≫ g = 0
  exact : (ShortComplex.mk f g map_comp).Exact
  epi : Epi g

/-- Tensoring a right exact sequence on the right preserves right exactness. -/
theorem tensorProduct_rightExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₁ F₂ F₃ G : CommRingSheafModule O}
    {f : F₁ ⟶ F₂} {g : F₂ ⟶ F₃}
    (h : RightExactSequence f g) :
    RightExactSequence
      (tensorProductMap f (𝟙 G)) (tensorProductMap g (𝟙 G)) := by
  sorry

/-! ## Pullback and colimits -/

/-- Pullback of modules along a continuous map and a map of structure sheaves.
The scalar map is written in the same `f_*` form as the project’s canonical
ringed-space module pullback. -/
noncomputable abbrev pullbackModule {X Y : TopCat.{v}}
    {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)] :
    CommRingSheafModule OY ⥤ CommRingSheafModule OX :=
  sheafModulePullbackAlong f α

/-- Pullback commutes with tensor products. -/
theorem pullback_tensorProduct_iso
    {X Y : TopCat.{v}} {OX : CommRingSheaf X} {OY : CommRingSheaf Y}
    (f : X ⟶ Y)
    (α : commRingSheafToRingSheaf OY ⟶
      (sheafRingPushforward f).obj (commRingSheafToRingSheaf OX))
    [((SheafOfModules.pushforward (F := Opens.map f) α).IsRightAdjoint)]
    (F G : CommRingSheafModule OY) :
    Nonempty
      ((pullbackModule f α).obj (tensorProductSheaf OY F G) ≅
        tensorProductSheaf OX ((pullbackModule f α).obj F)
          ((pullbackModule f α).obj G)) := by
  sorry

/-- Tensoring by a fixed module, as a functor on sheaves of modules. -/
noncomputable def tensorLeftFunctor {X : TopCat.{v}}
    (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    CommRingSheafModule O ⥤ CommRingSheafModule O where
  obj G := tensorProductSheaf O F G
  map f := tensorProductMap (𝟙 F) f
  map_id G := by
    exact tensorProductMap_id
  map_comp f g := by
    exact tensorProductMap_comp (𝟙 F) (𝟙 F) f g

/-- The tensor-by-`F` functor commutes with arbitrary colimits. -/
theorem tensorLeftFunctor_preserves_colimits
    {X : TopCat.{v}} (O : CommRingSheaf X) (F : CommRingSheafModule O) :
    PreservesColimitsOfSize (tensorLeftFunctor O F) := by
  sorry

/-! ## Direct sums and presentations used by permanence -/

/-- The categorical direct sum of a family of sheaves of modules. -/
noncomputable def directSum {X : TopCat.{v}} {O : CommRingSheaf X}
    {I : Type v} (F : I → CommRingSheafModule O) : CommRingSheafModule O :=
  colimit (Discrete.functor F)

/-- Tensor products distribute over direct sums of copies of the structure
sheaf. -/
theorem tensorProduct_directSum_structureSheaf_iso
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (I J : Type v) :
    Nonempty
      (tensorProductSheaf O
          (directSum (fun _ : I => SheafOfModules.unit
            (commRingSheafToRingSheaf O)))
          (directSum (fun _ : J => SheafOfModules.unit
            (commRingSheafToRingSheaf O))) ≅
        directSum (fun _ : I × J => SheafOfModules.unit
          (commRingSheafToRingSheaf O))) := by
  sorry

/-- The map in the standard tensor-product presentation. -/
noncomputable def tensorProductPresentationMap
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ : CommRingSheafModule O}
    {G₂ G₁ : CommRingSheafModule O}
    (f₂ : F₂ ⟶ F₁)
    (g₂ : G₂ ⟶ G₁) :
    (tensorProductSheaf O F₂ G₁ ⊞ tensorProductSheaf O F₁ G₂) ⟶
      tensorProductSheaf O F₁ G₁ :=
  biprod.desc
    (tensorProductMap f₂ (𝟙 G₁))
    (tensorProductMap (𝟙 F₁) g₂)

/-- The displayed two-presentation construction is right exact. -/
theorem tensorProduct_presentation_rightExact
    {X : TopCat.{v}} {O : CommRingSheaf X}
    {F₂ F₁ F : CommRingSheafModule O}
    {G₂ G₁ G : CommRingSheafModule O}
    {f₂ : F₂ ⟶ F₁} {f₁ : F₁ ⟶ F}
    {g₂ : G₂ ⟶ G₁} {g₁ : G₁ ⟶ G}
    (hF : RightExactSequence f₂ f₁)
    (hG : RightExactSequence g₂ g₁) :
    RightExactSequence
      (tensorProductPresentationMap f₂ g₂)
      (tensorProductMap f₁ g₁) := by
  sorry

/-! ## Permanence properties -/

/-- A commutative sheaf model viewed as the project’s ringed-space model, so
the chapter reuses the earlier definitions of local generation, finite type,
quasi-coherence, finite presentation, coherence, and local freeness. -/
noncomputable def underlyingRingedSpace {X : TopCat.{v}}
    (O : CommRingSheaf X) : RingedSpace :=
  { carrier := X
    structureSheaf := commRingSheafToRingSheaf O }

abbrev IsLocallyGenerated {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit08.locallyGenerated
    (X := underlyingRingedSpace O) F

abbrev IsFiniteType {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit09.finiteType
    (X := underlyingRingedSpace O) F

abbrev IsQuasiCoherent {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit10.IsQuasiCoherent
    (X := underlyingRingedSpace O) F

abbrev IsFinitePresentation {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit11.IsFinitePresentation
    (X := underlyingRingedSpace O) F

abbrev IsCoherent {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit12.IsCoherent
    (X := underlyingRingedSpace O) F

abbrev IsLocallyFree {X : TopCat.{v}} {O : CommRingSheaf X}
    (F : CommRingSheafModule O) : Prop :=
  Formalization.Books.Modules.Unit14.IsLocallyFree
    (X := underlyingRingedSpace O) F

/-- Tensor-product permanence for all seven properties listed in the source. -/
theorem tensorProduct_permanence
    {X : TopCat.{v}} {O : CommRingSheaf X}
    (F G : CommRingSheafModule O) :
    (IsLocallyGenerated F → IsLocallyGenerated G →
        IsLocallyGenerated (tensorProductSheaf O F G)) ∧
    (IsFiniteType F → IsFiniteType G →
        IsFiniteType (tensorProductSheaf O F G)) ∧
    (IsQuasiCoherent F → IsQuasiCoherent G →
        IsQuasiCoherent (tensorProductSheaf O F G)) ∧
    (IsFinitePresentation F → IsFinitePresentation G →
        IsFinitePresentation (tensorProductSheaf O F G)) ∧
    (IsFinitePresentation F → IsCoherent G →
        IsCoherent (tensorProductSheaf O F G)) ∧
    (IsCoherent F → IsCoherent G →
        IsCoherent (tensorProductSheaf O F G)) ∧
    (IsLocallyFree F → IsLocallyFree G →
        IsLocallyFree (tensorProductSheaf O F G)) := by
  sorry

end

end Formalization.Books.Modules.Unit16
